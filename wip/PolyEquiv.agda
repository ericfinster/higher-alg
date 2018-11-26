{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import PolyMonad

-- Equivalences of Polynomials
module wip.PolyEquiv where

  record _≃ₚ_ {ℓ} {I J : Type ℓ} (P : Poly I) (Q : Poly J) : Type ℓ where
    field

      Sort≃ : I ≃ J
      Op≃ : (i : I) → Op P i ≃ Op Q (–> Sort≃ i)
      Param≃ : {i : I} (f : Op P i) (j : I)
        → Param P f j ≃ Param Q (–> (Op≃ i) f) (–> Sort≃ j)

  open _≃ₚ_ public
  
  module _ {ℓ} {I J : Type ℓ} {P : Poly I} {Q : Poly J} (e : P ≃ₚ Q) where

    W≃-to : (i : I) → W P i → W Q (–> (Sort≃ e) i)
    W≃-to i (lf .i) = lf (–> (Sort≃ e) i)
    W≃-to i (nd (f , ϕ)) = nd (–> (Op≃ e i) f , λ j p →
      transport (W Q) (<–-inv-r (Sort≃ e) j) (W≃-to (<– (Sort≃ e) j) (ϕ (<– (Sort≃ e) j)
        (<– (Param≃ e f (<– (Sort≃ e) j))
          (transport! (Param Q (–> (Op≃ e i) f)) (<–-inv-r (Sort≃ e) j) p)))))

    W≃-from : (i : I) → W Q (–> (Sort≃ e) i) → W P i 
    W≃-from i (lf ._) = lf i
    W≃-from i (nd (f , ϕ)) = nd (<– (Op≃ e i) f , λ j p →
      W≃-from j (ϕ (–> (Sort≃ e) j) (transport (λ x → Param Q x (–> (Sort≃ e) j))
        (<–-inv-r (Op≃ e i) f) (–> (Param≃ e (<– (Op≃ e i) f) j) p))))

    postulate

      W≃-to-from : (i : I) (w : W Q (–> (Sort≃ e) i))
        → W≃-to i (W≃-from i w) == w

      W≃-from-to : (i : I) (w : W P i)
        → W≃-from i (W≃-to i w) == w

    W≃ : (i : I) → W P i ≃ W Q (–> (Sort≃ e) i)
    W≃ i = equiv (W≃-to i) (W≃-from i)
      (W≃-to-from i) (W≃-from-to i)

  -- Next, you could say what you mean by the idea that two
  -- relations are equal over an equivalence.
