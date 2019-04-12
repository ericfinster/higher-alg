{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import PolyMagma
open import Grafting
open import Substitution
open import Slice

module wip.SubstMonad {ℓ}  {I : Type ℓ} (P : Poly I) where

  open import wip.SubstUnits P
  open import wip.SubstSubst P 

  open BiasedLaws
  
  SubstBiasedLaws : BiasedLaws (SubstBiasedMgm P)
  unit-l SubstBiasedLaws (w , α) =
    pair= (subst-unit-l w) (subst-unit-l-frm w α)
  unit-r SubstBiasedLaws {f} κ = 
    let (w , α) = κ f (inl idp)
    in pair= (graft-unit P w) (subst-unit-r-frm κ)
  assoc SubstBiasedLaws {f} (w , α) κ ν =
    pair= (subst-assoc w κ ν ) (subst-assoc-frm w α κ ν)
  unit-l-frm SubstBiasedLaws (w , α) g n =
    ↓-Σ-weaken (λ x → Node P x g) (subst-node-unit-l w g n)
  unit-r-frm SubstBiasedLaws {f} κ g n =
    let (w , α) = κ f (inl idp)
    in ↓-Σ-weaken (λ x → Node P x g) (graft-unit-nd P w g n)
  assoc-frm SubstBiasedLaws (w , α) κ ν k g m h n o =
    ↓-Σ-weaken (λ x → Node P x k) (subst-node-assoc w κ ν g h k m n o)

  DblSlc : Poly (Ops (Subst P))
  DblSlc = Subst P // ⟪ SubstMgm P ⟫ 

  -- Here is the magma structure on the double slice.
  DblSlcMgm : PolyMagma DblSlc
  DblSlcMgm = SlcMgm (Subst P) ⟪ SubstMgm P ⟫
    (LawsInvar (SubstBiasedMgm P) SubstBiasedLaws)

  -- Here is the magma structure on the iteration of subst
  DblSubstMgm : PolyMagma (Subst (Subst P))
  DblSubstMgm = SubstMgm (Subst P)

  TrplSlc : Poly (Ops (DblSlc))
  TrplSlc = DblSlc // ⟪ DblSlcMgm ⟫ 

  TrplSlcMgm : PolyMagma TrplSlc
  μ TrplSlcMgm {(((i , f) , (w , α)) , ((pd , β) , e))} coh =
    μ-subst DblSlc (W↓ DblSlc ⟪ DblSlcMgm ⟫ coh) , {!!}
  μ-frm TrplSlcMgm {(((i , f) , (w , α)) , ((pd , β) , e))} coh =
    Frame↑ DblSlc ⟪ DblSlcMgm ⟫ {wαr = {!!} , {!!}}
      (μ-frm-subst DblSlc (W↓ DblSlc ⟪ DblSlcMgm ⟫ coh)) 

  something : {i : I} {f : Op P i}
    → (w : W P i) (α : Frame P w f)
    → (pd : W (Subst P) (i , f)) (β : Frame (Subst P) pd (w , α))
    → (r : ⟪ SubstMgm P ⟫ ((i , f) , (w , α)) (pd , β))
    → (c : Op DblSlc ((i , f) , (w , α)))
    → Type ℓ
  something w α pd β e ((x , y) , z) = {!!}

  -- encode : {i : I} {f : Op P i}
  --   → (w : W P i) (α : Frame P w f)
  --   → (pd : W (Subst P) (i , f)) (β : Frame (Subst P) pd (w , α))
  --   → (r : ⟪ SubstMgm P ⟫ ((i , f) , (w , α)) (pd , β))
  --   → (coh : W DblSlc ((i , f) , (w , α)))
  --   → (ζ : Frame DblSlc coh ((pd , β) , r))
  --   → ⟪ DblSlcMgm ⟫ (((i , f) , (w , α)) , (pd , β) , r) (coh , ζ)
  --   → ⟪ DblSubstMgm ⟫ (((i , f) , (w , α)) , (pd , β))
  --                     (W↓ (Subst P) ⟪ SubstMgm P ⟫ coh ,
  --                      Frame↓ (Subst P) ⟪ SubstMgm P ⟫ {wαr = (pd , β) , r} ζ)
  -- encode w α ._ ._ ._ (lf ._) ζ idp = {!coh!}
  -- encode ._ ._ ._ ._ ._ (nd (((pd , ._) , idp) , ϕ)) ζ idp = {!!}
  
  -- -- So look at the arguments above.  These will be exactly the
  -- -- colors of the triple slice, right.  And elimination of
  -- -- singletons says exactly that the colors can be *reduced*
  -- -- to the data displayed above.

  -- -- This means you should be able to *rewrite* this whole polynomial
  -- -- in a way which *does not* use the lower coherence.  So you will
  -- -- have to also rewrite the trees and so on, but okay.

  -- -- And now, what we see is that this should be exactly the double
  -- -- substitution polynomial for this simplified guy.  And that's
  -- -- the proof: the next multiplication can be obtained by transferring
  -- -- the multiplication we have already defined along this isomorphism.

  -- -- Okay, but thinking a bit more about that, the thing is, if you
  -- -- are saying that the thing is equivalent to some other guy, and
  -- -- that this is why you can define the multiplication, then that
  -- -- means that by transporting along this equivalence, you can *already*
  -- -- define the multiplication at this point.

  -- -- In other words, if you are actually claiming that there is a
  -- -- multiplication which does not use the more than the lower associativity,
  -- -- then you should actually be able to *define* this on the triple slice.
  -- -- I think that by writing this out, you will be able to see quickly
  -- -- what the actual idea is.

  -- -- decode : {i : I} {f : Op P i}
  -- --   → (w : W P i) (α : Frame P w f)
  -- --   → (pd : W (Subst P) (i , f)) (β : Frame (Subst P) pd (w , α))
  -- --   → (r : ⟪ SubstMgm P ⟫ ((i , f) , (w , α)) (pd , β))
  -- --   → (coh : W DblSlc ((i , f) , (w , α)))
  -- --   → (ζ : Frame DblSlc coh ((pd , β) , r))
  -- --   → ⟪ DblSubstMgm ⟫ (((i , f) , (w , α)) , (pd , β))
  -- --                     (W↓ (Subst P) ⟪ SubstMgm P ⟫ coh ,
  -- --                      Frame↓ (Subst P) ⟪ SubstMgm P ⟫ {wαr = (pd , β) , r} ζ)
  -- --   → ⟪ DblSlcMgm ⟫ (((i , f) , (w , α)) , (pd , β) , r) (coh , ζ)
  -- -- decode {i} {f} .(fst (μ-subst P pd)) .(snd (μ-subst P pd)) pd .(μ-frm-subst P pd) idp (lf .((i , f) , μ-subst P pd)) ζ rs = {!snd= rs!}

  -- --   -- where goal : LawsInvar (SubstBiasedMgm P) SubstBiasedLaws (lf ((i , f) , μ-subst P pd)) ◃
  -- --   --                apd (λ x →  μ-subst P pd , snd x) (fst= rs) 
  -- --   --                == apd (λ x → μ-subst P (fst x) , μ-frm-subst P (fst x)) (fst= rs) ▹ idp
  -- --   --       goal = {!!}

  -- --   where pd-is-corolla : corolla (Subst P) (μ-subst P pd) == pd
  -- --         pd-is-corolla = fst= (fst= rs)

  -- --         pd-corolla-frm : corolla-frm (Subst P) (μ-subst P pd) ==
  -- --                          μ-frm-subst P pd
  -- --                            [ (λ x → Frame (Subst P) x (μ-subst P pd)) ↓ pd-is-corolla ]
  -- --         pd-corolla-frm = snd= (fst= rs)

  -- -- decode w α pd β r (nd x) ζ rs = {!!}

  -- --   -- -- A biased relation becomes subdivision invariant
  -- --   -- -- by iteration.
  -- --   -- ToSubInvar : BiasedRel → SubInvar
  -- --   -- ToSubInvar Ψ (lf f) = η-rel Ψ f
  -- --   -- ToSubInvar Ψ (nd ((wα , r) , ϕ)) =
  -- --   --   γ-rel Ψ _ wα r (λ g n → μ-subst P (W↓ (ϕ g n)) , ToSubInvar Ψ (ϕ g n))
