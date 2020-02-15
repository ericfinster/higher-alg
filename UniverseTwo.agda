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
  μ₁ : (Γ : Ctx)
    → (δ : (p : CtxPos Γ) → Ctx)
    → (ε : (p : CtxPos Γ) → Tree₂ (δ p) (CtxTyp Γ p))
    → Ctx

  μ₁-transp : (Γ : Ctx) (A : Set)
    → (σ : Tree₂ Γ A)
    → Σ↓ Γ → A
  
  μ₁-transp-lcl : (Γ : Ctx)
    → (δ : (p : CtxPos Γ) → Ctx)
    → (ε : (p : CtxPos Γ) → Tree₂ (δ p) (CtxTyp Γ p))
    → Σ↓ (μ₁ Γ δ ε) → Σ↓ Γ

  μ₁-pos : (Γ : Ctx)
    → (δ : (p : CtxPos Γ) → Ctx)
    → (ε : (p : CtxPos Γ) → Tree₂ (δ p) (CtxTyp Γ p))
    → (p : CtxPos Γ) (q : CtxPos (δ p))
    → CtxPos (μ₁ Γ δ ε)

  μ₁-pos-fst : (Γ : Ctx)
    → (δ : (p : CtxPos Γ) → Ctx)
    → (ε : (p : CtxPos Γ) → Tree₂ (δ p) (CtxTyp Γ p))
    → CtxPos (μ₁ Γ δ ε) → CtxPos Γ

  μ₁-pos-snd : (Γ : Ctx)
    → (δ : (p : CtxPos Γ) → Ctx)
    → (ε : (p : CtxPos Γ) → Tree₂ (δ p) (CtxTyp Γ p))
    → (p : CtxPos (μ₁ Γ δ ε))
    → CtxPos (δ (μ₁-pos-fst Γ δ ε p))

  γ₂ : (Γ : Ctx) (A : Set) (σ : Tree₂ Γ A)
    → (δ : (p : CtxPos Γ) → Ctx)
    → (ε : (p : CtxPos Γ) → Tree₂ (δ p) (CtxTyp Γ p))
    → Tree₂ (μ₁ Γ δ ε) A

  data Tree₂ where
    lf₂ : (A : Set) → Tree₂ (η₁ A) A
    nd₂ : (Γ : Ctx) (A : Set) (E : Eqv (Σ↓ Γ) A)
      → (δ : (p : CtxPos Γ) → Ctx)
      → (ε : (p : CtxPos Γ) → Tree₂ (δ p) (CtxTyp Γ p))
      → Tree₂ (μ₁ Γ δ ε) A

  Pos₂ : {Γ : Ctx} {A : Set} → Tree₂ Γ A → Set
  Pos₂ (lf₂ A) = ⊥
  Pos₂ (nd₂ Γ A E δ ε) = ⊤ ⊔ Σ (CtxPos Γ) (λ p → Pos₂ (ε p))

  SrcCtx : {Γ : Ctx} {A : Set} (σ : Tree₂ Γ A)
    → Pos₂ σ → Ctx
  SrcCtx (lf₂ A) ()
  SrcCtx (nd₂ Γ A E δ ε) (inl unit) = Γ
  SrcCtx (nd₂ Γ A E δ ε) (inr (p , q)) = SrcCtx (ε p) q

  TgtSet : {Γ : Ctx} {A : Set} (σ : Tree₂ Γ A)
    → Pos₂ σ → Set
  TgtSet (lf₂ A) ()
  TgtSet (nd₂ Γ A E δ ε) (inl unit) = A
  TgtSet (nd₂ Γ A E δ ε) (inr (p , q)) = TgtSet (ε p) q

  Inh₂ : {Γ : Ctx} {A : Set} (σ : Tree₂ Γ A) (p : Pos₂ σ)
    → Eqv (Σ↓ (SrcCtx σ p)) (TgtSet σ p)
  Inh₂ (lf₂ A) ()
  Inh₂ (nd₂ Γ A E δ ε) (inl unit) = E
  Inh₂ (nd₂ Γ A E δ ε) (inr (p , q)) = Inh₂ (ε p) q

  postulate

    μ₁-pos-typ : (Γ : Ctx)
      → (δ : CtxPos Γ → Ctx)
      → (ε : (p : CtxPos Γ) → Tree₂ (δ p) (CtxTyp Γ p))
      → (p : CtxPos Γ) (q : CtxPos (δ p))
      → CtxTyp (μ₁ Γ δ ε) (μ₁-pos Γ δ ε p q) ↦ CtxTyp (δ p) q
    {-# REWRITE μ₁-pos-typ #-}

    μ₁-assoc : (Γ : Ctx)
      → (δ₀ : CtxPos Γ → Ctx)
      → (ε₀ : (p : CtxPos Γ) → Tree₂ (δ₀ p) (CtxTyp Γ p))
      → (δ₁ : (p : CtxPos (μ₁ Γ δ₀ ε₀)) → Ctx)
      → (ε₁ : (p : CtxPos (μ₁ Γ δ₀ ε₀)) → Tree₂ (δ₁ p) (CtxTyp (μ₁ Γ δ₀ ε₀) p))
      -- Don't know if the η-expanded version is better here ...
      -- → (δ₁ : (p : CtxPos Γ) (q : CtxPos (δ₀ p)) → Ctx)
      -- → (ε₁ : (p : CtxPos Γ) (q : CtxPos (δ₀ p)) → Tree₂ (δ₁ p q) (CtxTyp (δ₀ p) q))
      → μ₁ (μ₁ Γ δ₀ ε₀) δ₁ ε₁ ↦
        μ₁ Γ (λ p → μ₁ (δ₀ p) (λ q → δ₁ (μ₁-pos Γ δ₀ ε₀ p q)) ((λ q → ε₁ (μ₁-pos Γ δ₀ ε₀ p q))))
             (λ p → γ₂ (δ₀ p) (CtxTyp Γ p) (ε₀ p)
                              (λ q → δ₁ (μ₁-pos Γ δ₀ ε₀ p q))
                              (λ q → ε₁ (μ₁-pos Γ δ₀ ε₀ p q)) )
    {-# REWRITE μ₁-assoc #-}

  μ₁ nil δ ε = nil
  μ₁ (cns A B) δ ε =
    let Γ = δ (inl unit)
        a s = μ₁-transp Γ A (ε (inl unit)) s
        δ' s p = δ (inr (a s , p))
        ε' s p = ε (inr (a s , p))
        ψ s = μ₁ (B (a s)) (δ' s) (ε' s)
    in γ₁ Γ ψ

  μ₁-transp .(cns A (λ _ → nil)) A (lf₂ .A) (cns↓ a s) = a
  μ₁-transp .(μ₁ Γ δ ε) A (nd₂ Γ .A E δ ε) s =
    To E (μ₁-transp-lcl Γ δ ε s)

  μ₁-transp-lcl nil δ ε s = nil↓
  μ₁-transp-lcl (cns A B) δ ε s = 
    let Γ = δ (inl unit)
        a s = μ₁-transp Γ A (ε (inl unit)) s
        δ' s p = δ (inr (a s , p))
        ε' s p = ε (inr (a s , p))
        ψ s = μ₁ (B (a s)) (δ' s) (ε' s)
        s-fst = γ₁-fst Γ ψ s
        s-snd = γ₁-snd Γ ψ s
    in cns↓ (a s-fst) (μ₁-transp-lcl (B (a s-fst)) (δ' s-fst) (ε' s-fst) s-snd)

  μ₁-pos = {!!}
  μ₁-pos-fst = {!!}
  μ₁-pos-snd = {!!}

  γ₂ .(η₁ A) A (lf₂ .A) δ ε = ε (inl unit)
  γ₂ .(μ₁ Γ δ₀ ε₀) A (nd₂ Γ .A E δ₀ ε₀) δ₁ ε₁ = 
    nd₂ Γ A E δ₀' ε₀'

      where δ₁' : (p : CtxPos Γ) → CtxPos (δ₀ p) → Ctx
            δ₁' p q = δ₁ (μ₁-pos Γ δ₀ ε₀ p q)

            ε₁' : (p : CtxPos Γ) (q : CtxPos (δ₀ p))
              → Tree₂ (δ₁ (μ₁-pos Γ δ₀ ε₀ p q)) (CtxTyp (δ₀ p) q)
            ε₁' p q = ε₁ (μ₁-pos Γ δ₀ ε₀ p q)

            δ₀' : CtxPos Γ → Ctx
            δ₀' p = μ₁ (δ₀ p) (δ₁' p) (ε₁' p)

            ε₀' : (p : CtxPos Γ) → Tree₂ (δ₀' p) (CtxTyp Γ p)
            ε₀' p = γ₂ (δ₀ p) (CtxTyp Γ p) (ε₀ p) (δ₁' p) (ε₁' p)

  -- Okay.  So this means that the types do indeed work out, I think.
  -- Now, the point is that in the *next* dimension, we are going to
  -- elide the extra dependence in the type of μ.  And the hope is
  -- that by then directly exposing the dependence in the lowest
  -- dimension, we can in fact specialize the correct type of the
  -- lowest dimensional frame to be correct, where it will remain
  -- so in all higher dimensions.  It's a long shot.


  μ₂ : (Γ : Ctx) (A : Set)
    → (β : Tree₂ Γ A) 
    → (δ : (p : Pos₂ β) → Tree₂ (SrcCtx β p) (TgtSet β p))
    → Tree₂ Γ A
  μ₂ .(cns A (λ _ → nil)) A (lf₂ .A) δ₁ = lf₂ A
  μ₂ .(μ₁ Γ δ ε) A (nd₂ Γ .A E δ ε) δ₁ =
    let w = δ₁ (inl unit)
        δ₁' p q = δ₁ (inr (p , q))
        ε' p = μ₂ _ _ (ε p) (δ₁' p)
    in {! γ₂ Γ A w δ ε'!}

  -- Mmm.  It's happening again.  But there should be a way to write
  -- this function, no?  This was the point of unrolling. To get
  -- exactly here and see what the "pattern" was.  But so far, I don't
  -- think you really changed anything.

  -- So what gives? Are you just not seeing how this multiplication
  -- operation really *does* need to use the higher witnesses to
  -- finish.  I guess that is the most likely answer.  Nonetheless,
  -- I'm still not completely satisfied.

  -- Right.  So here the problem is that we do not end up in the
  -- same context.  If we have a function which computes the correct
  -- context, then is this compatible with what you were doing elsewhere?

  -- I think I see!  The idea would be to return the different context
  -- type.  Then, in your other file, you can explictly ask for
  -- equivalences corresponding to the correct types.  The filling
  -- equivalence will be tricky because it seems we will need to know
  -- how to transport some elements over or something.  Dunno.  Most
  -- likely this doesn't work.  But I'll push it until I can't go
  -- any further ....
