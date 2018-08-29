{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Substitution

module SubstCoh {I : Type₀} {P : Poly I} (F : FillingFamily P) where

    -- Substituting a trivial decoration
    -- gives back the tree
    substitute-unit : {i : I} (w : W P i)
      → substitute F w (λ ic n → lf ic) == w
    substitute-unit (lf i) = idp
    substitute-unit (nd {i} (c , δ)) =
      ap (λ x → nd (c , x))
         (λ= (λ j → λ= (λ p → substitute-unit (δ j p))))

    postulate
    
      substitute-unit-frm : {i : I} (w : W P i)
        → (c : γ P i) (f : Frame P w c) (x : F w c f)
        → flatten-frm F (corolla (P // F) (w , f , x)) == f [ (λ w' → Frame P w' c) ↓ substitute-unit w ]
        
    -- substitute-unit-frm (lf i) c f x = λ= (λ j → equiv-== (λ { (leaf i) → idp }))
    -- substitute-unit-frm (nd (c₀ , δ)) c f x = ↓-ap-in (λ w' → Frame P w' c) (λ x → nd (c₀ , x)) (↓-Π-in (λ {j} {k} q →
    --   ↓-equiv-in (λ { (stem p₀ l₀) (stem p₁ l₁) r → {!!} })))
    
    -- fst (f j) (stem p₀ (substitute-lf-to (λ {;i₁} → F) (δ ;j p) (λ ic n → lf ic) j l₀))
    -- fst (f k) (stem p₁ l₁)

    -- Hmmm, yeah, it's a bit annoying here that the Leaf fibration doesn't
    -- calculate.  Indeed.  If it did, it pretty much looks like this is a
    -- matter of sticking together a bunch of pathovers which already exist.

    -- So, should you reorganize a couple of these things to be in a slightly
    -- better position?  After all, you kind of wanted to do this in any case
    -- to have a consistent notation for the paper ...
