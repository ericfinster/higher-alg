{-# OPTIONS --without-K --rewriting --type-in-type #-}

open import Base
open import UniverseOne

module UniverseTwo where

  data Tree₂ : Ctx → Set → Set 

  -- I don't actually see how to fix the termination problem
  -- here.  Not 100% sure if it's a real problem or the just
  -- a hidding computation because of having to extract out
  -- the local tree....
  {-# TERMINATING #-}
  μ₂ : (Γ : Ctx)
    → (δ : (p : CtxPos Γ) → Ctx)
    → (ε : (p : CtxPos Γ) → Tree₂ (δ p) (CtxTyp Γ p))
    → Ctx

  μ₂-transp : (Γ : Ctx) (A : Set)
    → (σ : Tree₂ Γ A)
    → Σ↓ Γ → A
  
  μ₂-transp-lcl : (Γ : Ctx)
    → (δ : (p : CtxPos Γ) → Ctx)
    → (ε : (p : CtxPos Γ) → Tree₂ (δ p) (CtxTyp Γ p))
    → Σ↓ (μ₂ Γ δ ε) → Σ↓ Γ

  μ₂-pos : (Γ : Ctx)
    → (δ : (p : CtxPos Γ) → Ctx)
    → (ε : (p : CtxPos Γ) → Tree₂ (δ p) (CtxTyp Γ p))
    → (p : CtxPos Γ) (q : CtxPos (δ p))
    → CtxPos (μ₂ Γ δ ε)

  μ₂-pos-fst : (Γ : Ctx)
    → (δ : (p : CtxPos Γ) → Ctx)
    → (ε : (p : CtxPos Γ) → Tree₂ (δ p) (CtxTyp Γ p))
    → CtxPos (μ₂ Γ δ ε) → CtxPos Γ

  μ₂-pos-snd : (Γ : Ctx)
    → (δ : (p : CtxPos Γ) → Ctx)
    → (ε : (p : CtxPos Γ) → Tree₂ (δ p) (CtxTyp Γ p))
    → (p : CtxPos (μ₂ Γ δ ε))
    → CtxPos (δ (μ₂-pos-fst Γ δ ε p))

  γ₂ : (Γ : Ctx) (A : Set) (σ : Tree₂ Γ A)
    → (δ : (p : CtxPos Γ) → Ctx)
    → (ε : (p : CtxPos Γ) → Tree₂ (δ p) (CtxTyp Γ p))
    → Tree₂ (μ₂ Γ δ ε) A

  data Tree₂ where
    lf₂ : (A : Set) → Tree₂ (η₁ A) A
    nd₂ : (Γ : Ctx) (A : Set) (E : Eqv (Σ↓ Γ) A)
      → (δ : (p : CtxPos Γ) → Ctx)
      → (ε : (p : CtxPos Γ) → Tree₂ (δ p) (CtxTyp Γ p))
      → Tree₂ (μ₂ Γ δ ε) A

  Pos₂ : {Γ : Ctx} {A : Set} → Tree₂ Γ A → Set
  Pos₂ (lf₂ A) = ⊥
  Pos₂ (nd₂ Γ A E δ ε) = ⊤ ⊔ Σ (CtxPos Γ) (λ p → Pos₂ (ε p))

  SrcTyp₂ : {Γ : Ctx} {A : Set} (σ : Tree₂ Γ A)
    → Pos₂ σ → Ctx
  SrcTyp₂ (lf₂ A) ()
  SrcTyp₂ (nd₂ Γ A E δ ε) (inl unit) = Γ
  SrcTyp₂ (nd₂ Γ A E δ ε) (inr (p , q)) = SrcTyp₂ (ε p) q

  TgtTyp₂ : {Γ : Ctx} {A : Set} (σ : Tree₂ Γ A)
    → Pos₂ σ → Set
  TgtTyp₂ (lf₂ A) ()
  TgtTyp₂ (nd₂ Γ A E δ ε) (inl unit) = A
  TgtTyp₂ (nd₂ Γ A E δ ε) (inr (p , q)) = TgtTyp₂ (ε p) q

  Inh₂ : {Γ : Ctx} {A : Set} (σ : Tree₂ Γ A) (p : Pos₂ σ)
    → Eqv (Σ↓ (SrcTyp₂ σ p)) (TgtTyp₂ σ p)
  Inh₂ (lf₂ A) ()
  Inh₂ (nd₂ Γ A E δ ε) (inl unit) = E
  Inh₂ (nd₂ Γ A E δ ε) (inr (p , q)) = Inh₂ (ε p) q

  postulate

    μ₂-pos-typ : (Γ : Ctx)
      → (δ : CtxPos Γ → Ctx)
      → (ε : (p : CtxPos Γ) → Tree₂ (δ p) (CtxTyp Γ p))
      → (p : CtxPos Γ) (q : CtxPos (δ p))
      → CtxTyp (μ₂ Γ δ ε) (μ₂-pos Γ δ ε p q) ↦ CtxTyp (δ p) q
    {-# REWRITE μ₂-pos-typ #-}

    μ₂-assoc : (Γ : Ctx)
      → (δ₀ : CtxPos Γ → Ctx)
      → (ε₀ : (p : CtxPos Γ) → Tree₂ (δ₀ p) (CtxTyp Γ p))
      → (δ₁ : (p : CtxPos (μ₂ Γ δ₀ ε₀)) → Ctx)
      → (ε₁ : (p : CtxPos (μ₂ Γ δ₀ ε₀)) → Tree₂ (δ₁ p) (CtxTyp (μ₂ Γ δ₀ ε₀) p))
      -- Don't know if the η-expanded version is better here ...
      -- → (δ₁ : (p : CtxPos Γ) (q : CtxPos (δ₀ p)) → Ctx)
      -- → (ε₁ : (p : CtxPos Γ) (q : CtxPos (δ₀ p)) → Tree₂ (δ₁ p q) (CtxTyp (δ₀ p) q))
      → μ₂ (μ₂ Γ δ₀ ε₀) δ₁ ε₁ ↦
        μ₂ Γ (λ p → μ₂ (δ₀ p) (λ q → δ₁ (μ₂-pos Γ δ₀ ε₀ p q)) ((λ q → ε₁ (μ₂-pos Γ δ₀ ε₀ p q))))
             (λ p → γ₂ (δ₀ p) (CtxTyp Γ p) (ε₀ p)
                              (λ q → δ₁ (μ₂-pos Γ δ₀ ε₀ p q))
                              (λ q → ε₁ (μ₂-pos Γ δ₀ ε₀ p q)) )
    {-# REWRITE μ₂-assoc #-}

  μ₂ nil δ ε = nil
  μ₂ (cns A B) δ ε =
    let Γ = δ (inl unit)
        a s = μ₂-transp Γ A (ε (inl unit)) s
        δ' s p = δ (inr (a s , p))
        ε' s p = ε (inr (a s , p))
        ψ s = μ₂ (B (a s)) (δ' s) (ε' s)
    in γ₁ Γ ψ

  μ₂-transp .(cns A (λ _ → nil)) A (lf₂ .A) (cns↓ a s) = a
  μ₂-transp .(μ₂ Γ δ ε) A (nd₂ Γ .A E δ ε) s =
    To E (μ₂-transp-lcl Γ δ ε s)

  μ₂-transp-lcl nil δ ε s = nil↓
  μ₂-transp-lcl (cns A B) δ ε s = 
    let Γ = δ (inl unit)
        a s = μ₂-transp Γ A (ε (inl unit)) s
        δ' s p = δ (inr (a s , p))
        ε' s p = ε (inr (a s , p))
        ψ s = μ₂ (B (a s)) (δ' s) (ε' s)
        s-fst = γ₁-fst Γ ψ s
        s-snd = γ₁-snd Γ ψ s
    in cns↓ (a s-fst) (μ₂-transp-lcl (B (a s-fst)) (δ' s-fst) (ε' s-fst) s-snd)

  μ₂-pos = {!!}
  μ₂-pos-fst = {!!}
  μ₂-pos-snd = {!!}

  γ₂ .(η₁ A) A (lf₂ .A) δ ε = ε (inl unit)
  γ₂ .(μ₂ Γ δ₀ ε₀) A (nd₂ Γ .A E δ₀ ε₀) δ₁ ε₁ = 
    nd₂ Γ A E δ₀' ε₀'

      where δ₁' : (p : CtxPos Γ) → CtxPos (δ₀ p) → Ctx
            δ₁' p q = δ₁ (μ₂-pos Γ δ₀ ε₀ p q)

            ε₁' : (p : CtxPos Γ) (q : CtxPos (δ₀ p))
              → Tree₂ (δ₁ (μ₂-pos Γ δ₀ ε₀ p q)) (CtxTyp (δ₀ p) q)
            ε₁' p q = ε₁ (μ₂-pos Γ δ₀ ε₀ p q)

            δ₀' : CtxPos Γ → Ctx
            δ₀' p = μ₂ (δ₀ p) (δ₁' p) (ε₁' p)

            ε₀' : (p : CtxPos Γ) → Tree₂ (δ₀' p) (CtxTyp Γ p)
            ε₀' p = γ₂ (δ₀ p) (CtxTyp Γ p) (ε₀ p) (δ₁' p) (ε₁' p)

  -- Okay.  So this means that the types do indeed work out, I think.
  -- Now, the point is that in the *next* dimension, we are going to
  -- elide the extra dependence in the type of μ.  And the hope is
  -- that by then directly exposing the dependence in the lowest
  -- dimension, we can in fact specialize the correct type of the
  -- lowest dimensional frame to be correct, where it will remain
  -- so in all higher dimensions.  It's a long shot.
