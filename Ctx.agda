{-# OPTIONS --without-K --rewriting --type-in-type #-}

open import Base

module Ctx where

  --
  --  Contexts
  --
  
  data Ctx : Set where
    nil : Ctx
    cns : (A : Set) (B : A → Ctx) → Ctx

  CtxPos : Ctx → Set
  CtxPos nil = ⊥
  CtxPos (cns A B) = ⊤ ⊔ Σ A (λ a → CtxPos (B a))
  
  CtxTyp : (Γ : Ctx) (p : CtxPos Γ) → Set
  CtxTyp nil ()
  CtxTyp (cns A B) (inl unit) = A
  CtxTyp (cns A B) (inr (a , p)) = CtxTyp (B a) p
  
  data Σ↓ : Ctx → Set where
    nil↓ : Σ↓ nil
    cns↓ : {A : Set} {B : A → Ctx}
      → (a : A) (b : Σ↓ (B a))
      → Σ↓ (cns A B)

  γ₁ : (Γ : Ctx) (δ : Σ↓ Γ  → Ctx) → Ctx
  γ₁ nil δ = δ nil↓
  γ₁ (cns A B) δ = cns A (λ a → γ₁ (B a) (λ b → δ (cns↓ a b)))
  
  γ₁-fst : (Γ : Ctx)
    → (δ : Σ↓ Γ  → Ctx) 
    → (s : Σ↓ (γ₁ Γ δ))
    → Σ↓ Γ
  γ₁-fst nil δ s = nil↓
  γ₁-fst (cns A B) δ (cns↓ a s) =
    let δ' b = δ (cns↓ a b)
    in cns↓ a (γ₁-fst (B a) δ' s)
  
  γ₁-snd : (Γ : Ctx)
    → (δ : Σ↓ Γ  → Ctx) 
    → (s : Σ↓ (γ₁ Γ δ))
    → Σ↓ (δ (γ₁-fst Γ δ s))
  γ₁-snd nil δ s = s
  γ₁-snd (cns A B) δ (cns↓ a s) =
    let δ' b = δ (cns↓ a b)
    in γ₁-snd (B a) δ' s

  γ₁-pos-inl : (Γ : Ctx) (δ : Σ↓ Γ  → Ctx)
    → CtxPos Γ → CtxPos (γ₁ Γ δ)
  γ₁-pos-inl nil δ ()
  γ₁-pos-inl (cns A B) δ (inl unit) = inl unit
  γ₁-pos-inl (cns A B) δ (inr (a , p)) =
    let δ' b = δ (cns↓ a b)
    in inr (a , γ₁-pos-inl (B a) δ' p)

  γ₁-pos-inr : (Γ : Ctx) (δ : Σ↓ Γ  → Ctx)
    → (s : Σ↓ Γ)
    → CtxPos (δ s)
    → CtxPos (γ₁ Γ δ)
  γ₁-pos-inr nil δ nil↓ p = p
  γ₁-pos-inr (cns A B) δ (cns↓ a s) p = 
    let δ' b = δ (cns↓ a b)
    in inr (a , γ₁-pos-inr (B a) δ' s p)

  --
  --  2-Trees
  --
  
  data Tree₂ : Set → Set where
    lf₂ : (A : Set) → Tree₂ A
    nd₂ : (Γ : Ctx) (A : Set) (E : Eqv (Σ↓ Γ) A)
      → (δ : (p : CtxPos Γ) → Tree₂ (CtxTyp Γ p))
      → Tree₂ A

  Lf : {A : Set} → Tree₂ A → Set
  Lf (lf₂ A) = ⊤
  Lf (nd₂ Γ A E δ) = Σ (CtxPos Γ) (λ p → Lf (δ p))

  LfTyp : {A : Set} (β : Tree₂ A)
    → Lf β → Set
  LfTyp (lf₂ A) unit = A
  LfTyp (nd₂ Γ A E δ) (p , l) = LfTyp (δ p) l

  γ-lf : {A : Set} (β : Tree₂ A)
    → (δ : (l : Lf β) → Tree₂ (LfTyp β l))
    → Tree₂ A
  γ-lf (lf₂ A) δ = δ unit
  γ-lf (nd₂ Γ A E δ) δ₁ =
    nd₂ Γ A E (λ p → γ-lf (δ p) (λ l → δ₁ (p , l)))

  Pos₂ : {A : Set} → Tree₂ A → Set
  Pos₂ (lf₂ A) = ⊥
  Pos₂ (nd₂ Γ A E δ) = ⊤ ⊔ Σ (CtxPos Γ) (λ p → Pos₂ (δ p))

  SrcCtx : {A : Set} (σ : Tree₂ A)
    → Pos₂ σ → Ctx
  SrcCtx (lf₂ A) ()
  SrcCtx (nd₂ Γ A E δ) (inl unit) = Γ
  SrcCtx (nd₂ Γ A E δ) (inr (p , q)) = SrcCtx (δ p) q

  TgtSet : {A : Set} (σ : Tree₂ A)
    → Pos₂ σ → Set
  TgtSet (lf₂ A) ()
  TgtSet (nd₂ Γ A E δ) (inl unit) = A
  TgtSet (nd₂ Γ A E δ) (inr (p , q)) = TgtSet (δ p) q

  Inh₂ : {A : Set} (σ : Tree₂ A)
    → (p : Pos₂ σ)
    → Eqv (Σ↓ (SrcCtx σ p)) (TgtSet σ p)
  Inh₂ (lf₂ A) ()
  Inh₂ (nd₂ Γ A E δ) (inl unit) = E
  Inh₂ (nd₂ Γ A E δ) (inr (p , q)) = Inh₂ (δ p) q

  -- Okay.  I really, really want to write a terminating, well
  -- formed function which calculates the resulting context.
  
  -- If I recall, the trick to doing this was to first have
  -- one level substitution, and then to iterate.

  subst-ctx : (Γ : Ctx)
    → (δ : (p : CtxPos Γ) → Ctx)
    → (ε : (p : CtxPos Γ) → Eqv (Σ↓ (δ p)) (CtxTyp Γ p))
    → Ctx
  subst-ctx nil δ ε = nil
  subst-ctx (cns A B) δ ε =
    let Γ₀ = δ (inl unit)
        E₀ = ε (inl unit)
        a s = To E₀ s
        δ' s p = δ (inr (a s , p))
        ε' s p = ε (inr (a s , p)) 
    in γ₁ Γ₀ (λ s → subst-ctx (B (a s)) (δ' s) (ε' s))

  postulate
  
    subst-Σ↓ : (Γ : Ctx)
      → (δ : (p : CtxPos Γ) → Ctx)
      → (ε : (p : CtxPos Γ) → Eqv (Σ↓ (δ p)) (CtxTyp Γ p))
      → Eqv (Σ↓ (subst-ctx Γ δ ε)) (Σ↓ Γ)
    -- subst-Σ↓ nil δ ε = IdEqv (Σ↓ nil)
    -- subst-Σ↓ (cns A B) δ ε = {!!}

  -- Fantastic.  And now this is completely terminating....
  
  ∂₂ : {A : Set} → Tree₂ A → Ctx

  ∂₂-Eqv : {A : Set} (β : Tree₂ A)
    → Eqv (Σ↓ (∂₂ β)) A
  
  ∂₂ (lf₂ A) = cns A (λ _ → nil)
  ∂₂ (nd₂ Γ A E δ) = subst-ctx Γ (λ p → ∂₂ (δ p)) (λ p → ∂₂-Eqv (δ p))

  R (∂₂-Eqv (lf₂ A)) (cns↓ a₀ nil↓) a₁ = a₀ == a₁
  left-contr (∂₂-Eqv (lf₂ A)) (cns↓ a nil↓) = (a , idp) , λ { (a , idp) → idp }
  right-contr (∂₂-Eqv (lf₂ A)) a = (cns↓ a nil↓ , idp) , λ { (cns↓ a nil↓ , idp) → idp }
  ∂₂-Eqv (nd₂ Γ A E δ) = E ∘ subst-Σ↓ Γ _ _

  --
  --  Now on to two dim'l substitution ...
  --
  
  data FramedTree : Ctx → Set → Set where
    frm : {A : Set} → (β : Tree₂ A) → FramedTree (∂₂ β) A

  FramedPos : {Γ : Ctx} {A : Set} → FramedTree Γ A → Set
  FramedPos (frm β) = Pos₂ β

  FramedSrcCtx : {Γ : Ctx} {A : Set} (σ : FramedTree Γ A)
    → FramedPos σ → Ctx
  FramedSrcCtx (frm β) = SrcCtx β

  FramedTgtSet : {Γ : Ctx} {A : Set} (σ : FramedTree Γ A)
    → FramedPos σ → Set
  FramedTgtSet (frm β) = TgtSet β

  FramedInh : {Γ : Ctx} {A : Set} (σ : FramedTree Γ A)
    → (p : FramedPos σ)
    → Eqv (Σ↓ (FramedSrcCtx σ p)) (FramedTgtSet σ p)
  FramedInh (frm β) = Inh₂ β

  γ₂ : {A : Set} (σ : Tree₂ A)
    → (δ : (p : CtxPos (∂₂ σ)) → Tree₂ (CtxTyp (∂₂ σ) p))
    → Tree₂ A
  γ₂ (lf₂ A) δ = lf₂ A
  γ₂ (nd₂ Γ A E δ) δ₁ =
    nd₂ Γ A E (λ p → γ₂ (δ p) (λ p → {!!}))

  γ-frm : {Γ : Ctx} {A : Set}
    → (σ : FramedTree Γ A)
    → (δ : (p : CtxPos Γ) → Ctx)
    → (ε : (p : CtxPos Γ) → FramedTree (δ p) (CtxTyp Γ p))
    → FramedTree {!!} A
  γ-frm = {!!}
    
  μ₂ : {Γ : Ctx} {A : Set}
    → (σ : FramedTree Γ A)
    → (δ : (p : FramedPos σ) → FramedTree (FramedSrcCtx σ p) (FramedTgtSet σ p))
    → FramedTree Γ A

  μ₂ (frm (lf₂ A)) _ = frm (lf₂ A)
  μ₂ (frm (nd₂ Γ A E δ)) δ₁ with δ₁ (inl unit)
  μ₂ (frm (nd₂ .(∂₂ β) A E δ)) δ₁ | frm β = {!frm (γ₂ β (λ p → ?))!}
