{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Substitution
open import SubstCoh

module Globularity where

  module _ {ℓ} {I : Type ℓ} {P : Poly I} (R : PolyRel P)
    (X : Refinement R) (Y : Refinement (FlattenRel (ΣR R X))) where

    private
      R₀ = ΣR R X
      R₁ = ΣR (FlattenRel R₀) Y
      
    postulate

      flatten-flatten : {i : I} {f : Op P i}
        → (w : W P i) (α : Frame P w f) (r : R₀ w f α)
        → (coh : W ((P // R₀) // R₁) ((i , f) , (w , α , r)))
        → flatten R₀ (flatten R₁ coh) == w

      flatten-frm-flatten : {i : I} {f : Op P i}
        → (w : W P i) (α : Frame P w f) (r : R₀ w f α)
        → (coh : W ((P // R₀) // R₁) ((i , f) , (w , α , r)))
        → flatten-frm R₀ (flatten R₁ coh) == α
            [ (λ w₁ → Frame P w₁ f) ↓ flatten-flatten w α r coh ]

      flatten-bd-flatten : {i : I} {f : Op P i}
        → (w : W P i) (α : Frame P w f) (r : R₀ w f α)
        → (coh : W ((P // R₀) // R₁) ((i , f) , (w , α , r)))
        → (s : R₀ (flatten R₀ (flatten R₁ coh)) f (flatten-frm R₀ (flatten R₁ coh)))
        → (q : s == r [ (λ x → R₀ (fst x) f (snd x)) ↓  pair= (flatten-flatten w α r coh) (flatten-frm-flatten w α r coh) ])
        → bd-frame R₀ (flatten R₁ coh) == flatten-frm R₁ coh
            [ Frame (P // R₀) (flatten R₁ coh) ↓ pair= (flatten-flatten w α r coh) (↓-Σ-in (flatten-frm-flatten w α r coh) q) ]

  -- Okay, nice.  It's exactly what I thought: the baez-dolan frame turns into the flatten
  -- frame in the next dimension.
