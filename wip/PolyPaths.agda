{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import PolyMonad

module wip.PolyPaths where

  -- Some lemmas about polynomials which are equal.

 W→ : ∀ {ℓ} {I J : Type ℓ} {P : Poly I} {Q : Poly J}
   → (p : (I , P) == (J , Q))
   → (i : I) → W P i → W Q (–> (coe-equiv (fst= p)) i)
 W→ idp i w = w

 -- Okay.  So far so good.  Now what did you want to say?
 -- Ah, right, about flatten.

 flatn-nat : ∀ {ℓ} {I J : Type ℓ} {P : Poly I} {R : PolyRel P} {Q : Poly J}
   → (p : (J , Q) == (Ops P , (P // R)))
   → (j : J) (w : W Q j)
   → flatn R (W→ p j w) == {!W→ !}
 flatn-nat p = {!!}
