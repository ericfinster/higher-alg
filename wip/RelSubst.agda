{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Substitution
open import PolyMonad

module wip.RelSubst {ℓ} where

  -- Okay, let's see about how the relative substitution
  -- monad might work.

  module _ {I : Type ℓ} (P : Poly I) (M : PolyMonad P) (X : Ops P → Type ℓ) where

    Q : Poly I
    Op Q i = Σ (Op P i) (λ f → X (i , f)) 
    Param Q (f , x) j = Param P f j

    -- Okay, so that's our total polynomial.
    -- Next idea is that it has a relation.

    w-prj : {i : I} → W Q i → W P i
    w-prj (lf i) = lf i
    w-prj (nd ((f , x) , ϕ)) = nd (f , λ j p → w-prj (ϕ j p))

    w-frm : {i : I} (f : Op P i) (x : X (i , f)) (w : W Q i)
      → Frame Q w (f , x)
      → Frame P (w-prj w) f
    w-frm = {!!}

    R : PolyRel Q
    R (i , f , x) (w , α) =
      ⟪ Mgm M ⟫ (i , f) (w-prj w , w-frm f x w α)

    -- So far, so good.  Now what?
    P' : Poly (Σ I (λ i → Σ (Op P i) (λ f → X (i , f))))
    P' = Q // R

    -- Hmmm.  Okay, I see.  So after a single slice,
    -- the sorts also are different.  And this is going
    -- to persist.


    Mgm' : PolyMagma P'
    μ Mgm' = {!μ (Mgm M)!}
    μ-frm Mgm' = {!!}

    M' : PolyMonad P'
    Mgm M' = {!!}
    Coh M' = {!!}
