{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Biased
-- open import wip.BiasedRel

module wip.SubstMonad {ℓ}  where

  module _ {I : Type ℓ} (P : Poly I) where

    -- The polynomial of tree substitutions
    SubstPoly : Poly (Ops P)
    Op SubstPoly = InFrame P 
    Param SubstPoly (w , _) g = Node P w g

    open BiasedMgm
    open BiasedLaws
    open import Grafting P
    open import Substitution P
    open import wip.SubstUnits P
    open import wip.SubstSubst P 

    SubstBiasedMgm : BiasedMgm SubstPoly
    η SubstBiasedMgm = subst-η
    η-frm SubstBiasedMgm = subst-η-frm
    γ SubstBiasedMgm (w , α) κ = subst w κ , subst-frm-∘ α κ
    γ-frm SubstBiasedMgm (w , α) κ = subst-node-eqv w κ

    SubstMgm : PolyMagma SubstPoly
    SubstMgm = BsdMgm SubstPoly SubstBiasedMgm

    SubstBiasedLaws : BiasedLaws SubstPoly SubstBiasedMgm
    unit-l SubstBiasedLaws (w , α) =
      pair= (subst-unit-l w) (subst-unit-l-frm w α)
    unit-r SubstBiasedLaws {f} κ = 
      let (w , α) = κ f (inl idp)
      in pair= (graft-unit w) (subst-unit-r-frm κ)
    assoc SubstBiasedLaws {f} (w , α) κ ν =
      pair= (subst-assoc w κ ν ) (subst-assoc-frm w α κ ν)
    unit-l-frm SubstBiasedLaws (w , α) g n =
      ↓-Σ-weaken (λ x → Node P x g) (subst-node-unit-l w g n)
    unit-r-frm SubstBiasedLaws {f} κ g n =
      let (w , α) = κ f (inl idp)
      in ↓-Σ-weaken (λ x → Node P x g) (graft-unit-nd w g n)
    assoc-frm SubstBiasedLaws (w , α) κ ν k g m h n o =
      ↓-Σ-weaken (λ x → Node P x k) (subst-node-assoc w κ ν g h k m n o)

