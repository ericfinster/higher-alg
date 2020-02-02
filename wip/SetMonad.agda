{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import PolyMagma
open import Substitution
open import Slice
open import WPaths

module wip.SetMonad where

  module _ {ℓ} {I : Type ℓ} (P : Poly I) (M : PolyMagma P) where

    SimpleSlice : Poly (Ops P)
    Op SimpleSlice (i , f) = Σ (W P i) (λ w → μ M w == f)
    Param SimpleSlice (w , _) = Node P w

  record SetMgm {ℓ} {I : Type ℓ} (P : Poly I) (M : PolyMagma P) : Type ℓ where
    field

      op-is-set : (i : I) → is-set (Op P i)

  open SetMgm

  module _ {ℓ} {I : Type ℓ} (P : Poly I) (M : PolyMagma P) (S : SetMgm P M) where

    Claim : PolyMagma (SimpleSlice P M)
    μ Claim {i , f} pd = {!!} , {!!}
    μ-frm Claim pd = {!!}

    Repeat : {i : I} (f : Op P i) → is-set (Op (SimpleSlice P M) (i , f))
    Repeat {i} f = Σ-level (W-level P (op-is-set S) i) (λ w → {!!})
    
