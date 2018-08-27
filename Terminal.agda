{-# OPTIONS --without-K --rewriting --type-in-type #-}

open import HoTT
open import Util
open import Polynomial
open import Substitution
open import Morphism

-- Attempting to construct the terminal cart-poly-monad.
module Terminal where

  𝕌 : Poly ⊤
  γ 𝕌 unit = Type₀
  ρ 𝕌 X unit = X

  TermFamily : {I : Type₀} (P : Poly I) → FillingFamily P
  TermFamily P w c f = ⊤

  TermDomain : {I : Type₀} (P : Poly I) → PolyDomain P
  F (TermDomain P) = TermFamily P
  H (TermDomain P) = TermDomain (P // TermFamily P)

  module _ {I : Type₀} {P : Poly I} (F₀ : FillingFamily P) where

    record BDWitness {i : I} {c : γ P i} (pd : W (P // F₀) (i , c))
      (w : W P i) (f₀ : Frame P w c) (x₀ : F₀ w c f₀)
      (f₁ : Frame (P // F₀) pd (w , f₀ , x₀)) : Type₀ where
      constructor bd-wit
      field
        p₀ : w == flatten F₀ pd
        p₁ : f₀ == flatten-frm F₀ pd [ (λ a → Frame P a c) ↓ p₀ ]
        p₂ : f₁ == bd-frame F₀ pd [ (λ a → Frame (P // F₀) pd a) ↓ pair= p₀ (↓-Σ-in p₁ (to-transp-↓ (uncurry (λ a → F₀ a c)) (pair= p₀ p₁) x₀)) ] 

    -- The canonical extension, adding a witness that fillers are always
    -- in baez-dolan frames.
    BDExt : (F₁ : FillingFamily (P // F₀)) → Extension F₁
    BDExt F₁ {i , c} pd (w , f₀ , x₀) f₁ x₁ = BDWitness pd w f₀ x₀ f₁ 

  {-# TERMINATING #-}
  BDDomain : {I : Type₀} (P : Poly I) (F₀ : FillingFamily P)
    → PolyDomain (P // F₀)
    → PolyDomain (P // F₀)
  F (BDDomain P F₀ D) = ΣFam (F D) (BDExt F₀ (F D))
  H (BDDomain P F₀ D) = Domain← (ExtendedFst (F D) (BDExt F₀ (F D))) (BDDomain (P // F₀) (F D) (H D))


  -- So, here is the version that you had before.

  -- -- I see, and I think here again, we shoul have a kind of equivalence.
  -- postulate

  --   compat : {I : Type₀} {P : Poly I} (F : FillingFamily P) (E : Extension F)
  --     → ΣPoly (ExtOver F E) == P // ExtendedFamily F E [ Poly ↓ {!!} ]

  --   BDExtension : {I : Type₀} {P : Poly I}
  --     → (F₀ : FillingFamily P) (F₁ : FillingFamily (P // F₀))
  --     → Extension F₁

  --   CanExtend : {I : Type₀} {P : Poly I} (F : FillingFamily P) (E : Extension F)
  --     → PolyDomain (P // F) → PolyDomain (P // ExtendedFamily F E)

  -- -- Something like this is what you had in mind.  Except does this version skip
  -- -- too much? Yeah, something is fishy about this guy.  Or I'm not completely
  -- -- sure.  Maybe it's actually okay.  I have no idea what to do about termination ....
  -- {-# TERMINATING #-}
  -- BDDomain : {I : Type₀} {P : Poly I} (D : PolyDomain P) → PolyDomain P
  -- F (BDDomain {I} {P} D) = F D
  -- F (H (BDDomain {I} {P} D)) = ExtendedFamily (F (H D)) (BDExtension (F D) (F (H D)))
  -- H (H (BDDomain {I} {P} D)) = CanExtend (F (H D)) (BDExtension (F D) (F (H D))) (BDDomain (H (H D)))

