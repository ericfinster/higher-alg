{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Substitution

module Multiplicative where

  record PolyMagma {ℓ} {I : Type ℓ} (P : Poly I) : Type ℓ where
    field

      μ : {i : I} (w : W P i) → Op P i
      μ-frm : {i : I} (w : W P i) → Frame P w (μ w)

  open PolyMagma
  
  _//_ : ∀ {ℓ} {I : Type ℓ} (P : Poly I) (M : PolyMagma P) → Poly (Ops P)
  Op (P // M) (i , f) = Σ (W P i) (λ w → Σ (Frame P w f) (λ α → (f , α) == (μ M w , μ-frm M w))) 
  Param (P // M) (w , α , e) = Node P w 

  module _ {ℓ} {I : Type ℓ} (P : Poly I) (M : PolyMagma P) where

    to-subst : {f : Ops P} (w : W (P // M) f) → W (Subst P) f
    to-subst (lf f) = lf f
    to-subst (nd ((w , α , e) , β)) = nd ((w , α) , λ g n → to-subst (β g n))

    postulate

      N : PolyMagma (P // M)

      ax₀ : {f : Ops P} (w : W (P // M) f) →
        (fst (μ N w) , fst (snd (μ N w))) == μ-subst P (to-subst w)

      -- Okay, this one is slightly more complicated.
      ax₁ : {f : Ops P} (w : W (P // M) f) →
        μ-frm N w == {!!}

      -- Probably to stay in the slice polynomial, you
      -- should write the iterated substitution and frame
      -- functions directly with their types.

  record Monad {ℓ} {I : Type ℓ} (P : Poly I) : Type ℓ where
    coinductive
    field

      M : PolyMagma P
      H : Monad (P // M)

