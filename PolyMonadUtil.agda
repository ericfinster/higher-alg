{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import PolyMonads

module PolyMonadUtil where

  -- Okay, I'm going to put here coherences and stuff for monads.

  module _ {I : Type₀} (M : Mnd I) where

    μρ-snd-coh : {i : I} {c : γ M i}
                 (δ : (p : ρ M c) → γ M (τ M p))
                 (p : ρ M (μ M c δ)) →
                 τ M (μρ-snd M δ p) == τ M p
    μρ-snd-coh δ p = ap (τ M) (μρ-η M δ p)
