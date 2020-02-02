{-# OPTIONS --without-K --rewriting --type-in-type #-}

open import HoTT

-- The Universe
module wip.Universe  where

  Poly : Set → Set → Set
  Poly I J = (A : Set) → (A → I) → J → Set

  data 𝕌Tr₁ : Set → (N : Set) → (N → Set) → Set where
    lf₁ : 𝕌Tr₁ ⊤ ⊥ (λ { () })
    nd₁ : (A : Set)
          → (L : A → Set)
          → (N : A → Set) (Nt : (a : A) → N a → Set)
          → 𝕌Tr₁ (Σ A L) (⊤ ⊔ (Σ A N))
                 (λ { (inl tt) → A ; (inr (a , n)) → Nt a n })

  -- Okay, yeah, so there's the first guy in the universe.  Now, what
  -- should the monad structure look like?

  𝕌Mgm₁ : ∀ L N τ → 𝕌Tr₁ L N τ → Set
  𝕌Mgm₁ L N τ tr = L

  -- Now, let's pass to the next phase.
  𝕌Slc : Poly Set Set
  𝕌Slc N τ L = 𝕌Tr₁ L N τ

  data 𝕌Tr₂ : Set → (L : Set) → (L → Set) → (N : Set) → (N → Set) → Set where
    lf₂ : (A : Set) → 𝕌Tr₂ A ⊤ (λ _ → A) ⊥ (λ { () })
    nd₂ : (A : Set) → 𝕌Tr₂ {!!} {!!} {!!} {!!} {!!}

  -- So just what is you goal here?  Well, I mean, I think the idea is
  -- that you want to implement this idea that types are polynomial
  -- algebras.  And in order to do this, you have to give some kind of
  -- syntatic presentation of the formation, introduction, elimination
  -- and computation rules of these higher opetopic equality types.
  -- And that is the part which is still somewhat unclear.

  -- That's right.  And so the question is, using this technique, is it
  -- in fact possible to, if not implement, at least write out the types
  -- of what such a sequence of families would look like?
