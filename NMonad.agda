{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import WPaths
open import Substitution
open import PolyMonad

module NMonad where

  module _ {ℓ} {I : Type ℓ} (P : Poly I) (M : PolyMagma P) (Ψ : CohWit P M) where

    TrivWit : CohWit (P // M) (slc-mgm P M Ψ)
    TrivWit {i , .(μ M w)} {w , idp} pd = pair= {!!} {!!}
