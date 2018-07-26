{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Substitution

module SubstCoh {I : Type₀} {P : Poly I} (F : FillingFamily P) where

    -- Substituting a trivial decoration
    -- gives back the tree
    substitute-unit : {i : I} (w : W P i)
      → w == substitute F w (λ ic n → lf ic) 
    substitute-unit (lf i) = idp
    substitute-unit (nd {i} (c , δ)) =
      ap (λ x → nd (c , x))
         (λ= (λ j → λ= (λ p → substitute-unit (δ j p))))

    -- substitute-unit-frm : {i : I} (w : W P i)
    --   → (c : γ P i) (f : Frame P w c) (x : F w c f)
    --   → f == flatten-frm F (corolla (P // F) (w , f , x)) [ (λ w' → Frame P w' c) ↓ substitute-unit w ]
    -- substitute-unit-frm (lf i) c f x = {!!}
    -- substitute-unit-frm (nd x₁) c f x = {!!}

