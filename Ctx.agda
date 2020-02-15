{-# OPTIONS --without-K --rewriting --type-in-type #-}

open import Base

module Ctx where

  --
  --  Contexts
  --
  
  data Ctx : Set where
    nil : Ctx
    cns : (A : Set) (B : A → Ctx) → Ctx

  data CtxPos : Ctx → Set where
    cns-here : (A : Set) (B : A → Ctx) → CtxPos (cns A B)
    cns-there : (A : Set) (B : A → Ctx)
      → (a : A) (p : CtxPos (B a))
      → CtxPos (cns A B)

  CtxTyp : (Γ : Ctx) (p : CtxPos Γ) → Set
  CtxTyp .(cns A B) (cns-here A B) = A
  CtxTyp .(cns A B) (cns-there A B a p) = CtxTyp (B a) p
  
  data Σ↓ : Ctx → Set where
    nil↓ : Σ↓ nil
    cns↓ : {A : Set} {B : A → Ctx}
      → (a : A) (b : Σ↓ (B a))
      → Σ↓ (cns A B)

  γ₁ : (Γ : Ctx) (δ : Σ↓ Γ  → Ctx) → Ctx
  γ₁ nil δ = δ nil↓
  γ₁ (cns A B) δ = cns A (λ a → γ₁ (B a) (λ b↓ → δ (cns↓ a b↓)))
  
  γ₁-fst : (Γ : Ctx)
    → (δ : Σ↓ Γ  → Ctx) 
    → (s : Σ↓ (γ₁ Γ δ))
    → Σ↓ Γ
  γ₁-fst nil δ s = nil↓
  γ₁-fst (cns A B) δ (cns↓ a s) =
    cns↓ a (γ₁-fst (B a) (λ b↓ → δ (cns↓ a b↓)) s)
  
  γ₁-snd : (Γ : Ctx)
    → (δ : Σ↓ Γ  → Ctx) 
    → (s : Σ↓ (γ₁ Γ δ))
    → Σ↓ (δ (γ₁-fst Γ δ s))
  γ₁-snd nil δ s = s
  γ₁-snd (cns A B) δ (cns↓ a s) =
    γ₁-snd (B a) (λ b↓ → δ (cns↓ a b↓)) s

  γ₁-pos-inl : (Γ : Ctx) (δ : Σ↓ Γ  → Ctx)
    → CtxPos Γ → CtxPos (γ₁ Γ δ)
  γ₁-pos-inl = {!!}

  γ₁-pos-inr : (Γ : Ctx) (δ : Σ↓ Γ  → Ctx)
    → (s : Σ↓ Γ)
    → CtxPos (δ s)
    → CtxPos (γ₁ Γ δ)
  γ₁-pos-inr = {!!}
  
  --
  --  Equivalences
  --

  record Eqv (A B : Set) : Set where
    field
      Wit : A → B → Set
      To : A → B
      ToWit : (a : A) → Wit a (To a)
      From : B → A
      FromWith : (b : B) → Wit (From b) b
      -- ... and the coherences ....
      
  open Eqv public

  --
  --  2-Trees
  --
  
  data Tree₂ : Set → Set where
    lf₂ : (A : Set) → Tree₂ A
    nd₂ : (Γ : Ctx) (A : Set) (E : Eqv (Σ↓ Γ) A)
      → (δ : (p : CtxPos Γ) → Tree₂ (CtxTyp Γ p))
      → Tree₂ A

  -- Okay, one idea is to define the type of "spines"
  -- which will just be the same thing as elements
  -- of the bounding context.  Then prove some equivalences
  -- and so on.
  
  -- Annoying the termination here, but I don't immediately
  -- see a better way to do it ...
  
  {-# TERMINATING #-}
  ∂₂ : {A : Set} → Tree₂ A → Ctx
  μ₁ : (Γ : Ctx) (δ : (p : CtxPos Γ) → Tree₂ (CtxTyp Γ p)) → Ctx
  
  Σ↓↓ : {A : Set} (σ : Tree₂ A)
    → Σ↓ (∂₂ σ) → A

  Σ↓↑ : {A : Set} (σ : Tree₂ A)
    → A → Σ↓ (∂₂ σ)
  Σ↓↑ = {!!}
  
  Σ↓↓-μ : (Γ : Ctx) (δ : (p : CtxPos Γ) → Tree₂ (CtxTyp Γ p))
    → Σ↓ (μ₁ Γ δ) → Σ↓ Γ

  ∂₂ (lf₂ A) = cns A (λ _ → nil)
  ∂₂ (nd₂ Γ A E δ) = μ₁ Γ δ

  μ₁ nil δ = nil
  μ₁ (cns A B) δ =
    let w = δ (cns-here A B)
        a s = Σ↓↓ w s
        δ' s p = δ (cns-there A B (a s) p)
        ϕ s = μ₁ (B (a s)) (δ' s)
    in γ₁ (∂₂ w) ϕ
  
  Σ↓↓ (lf₂ A) (cns↓ a _) = a
  Σ↓↓ (nd₂ Γ A E δ) s =
    To E (Σ↓↓-μ Γ δ s)

  Σ↓↓-μ nil δ s = s
  Σ↓↓-μ (cns A B) δ s = 
    let w = δ (cns-here A B)
        a s = Σ↓↓ w s
        δ' s p = δ (cns-there A B (a s) p)
        ϕ s = μ₁ (B (a s)) (δ' s)
        s₀ = γ₁-fst (∂₂ w) ϕ s
        s₁ = γ₁-snd (∂₂ w) ϕ s
    in cns↓ (a s₀) (Σ↓↓-μ (B (a s₀)) (δ' s₀) s₁)

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

  μ₁-pos : (Γ : Ctx) (δ : (p : CtxPos Γ) → Tree₂ (CtxTyp Γ p))
    → (p : CtxPos Γ) → CtxPos (∂₂ (δ p)) → CtxPos (μ₁ Γ δ)

  μ₁-pos nil δ () q
  μ₁-pos (cns A B) δ (cns-here .A .B) q =
    let w = δ (cns-here A B)
        a s = Σ↓↓ w s
        δ' s p = δ (cns-there A B (a s) p)
        ϕ s = μ₁ (B (a s)) (δ' s)
    in γ₁-pos-inl (∂₂ w) ϕ q
  μ₁-pos (cns A B) δ (cns-there .A .B a₀ p) q = 
    let w = δ (cns-here A B)
        a s = Σ↓↓ w s
        δ' s p = δ (cns-there A B (a s) p)
        ϕ s = μ₁ (B (a s)) (δ' s)
    in γ₁-pos-inr (∂₂ w) ϕ (Σ↓↑ w a₀) {!!}


  --
  --  Okay, next step, see if you can write grafting
  --  and substitution for 2-trees.
  --
  
  postulate
    
    μ₁-pos-typ : (Γ : Ctx) (δ : (p : CtxPos Γ) → Tree₂ (CtxTyp Γ p))
      → (p : CtxPos Γ) (q : CtxPos (∂₂ (δ p)))
      → CtxTyp (μ₁ Γ δ) (μ₁-pos Γ δ p q) ↦ CtxTyp (∂₂ (δ p)) q
    {-# REWRITE μ₁-pos-typ #-}
    
  μ₂ : {A : Set} (σ : Tree₂ A)
    → (δ : (p : Pos₂ σ) → Σ (Tree₂ (TgtSet σ p)) (λ τ → ∂₂ τ == SrcCtx σ p))
    → Tree₂ A

  γ₂ : {A : Set} (σ : Tree₂ A)
    → (δ : (p : CtxPos (∂₂ σ)) → Tree₂ (CtxTyp (∂₂ σ) p))
    → Tree₂ A

  μ₂ (lf₂ A) δ = lf₂ A
  μ₂ (nd₂ Γ A E δ) δ₁ with δ₁ (inl unit)
  μ₂ (nd₂ .(∂₂ w) A E δ) δ₁ | (w , idp) =
    γ₂ w (λ p → μ₂ (δ p) (λ q → δ₁ (inr (p , q))))

  γ₂ (lf₂ A) δ = lf₂ A
  γ₂ (nd₂ Γ A E δ) δ₁ =
    nd₂ Γ A E (λ p → γ₂ (δ p) (λ q → δ₁ (μ₁-pos Γ δ p q)))


