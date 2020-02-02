{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import PolyMagma
open import Grafting
open import Substitution
open import Slice
open import wip.PolyEquiv

module wip.SubstMonad  where

  module _ {ℓ}  {I : Type ℓ} (P : Poly I) where
  
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

    SubstInvar : SubInvar (Subst P) ⟪ SubstMgm P ⟫
    SubstInvar = LawsInvar (SubstBiasedMgm P) SubstBiasedLaws

    globularity : {i : I} {f : Op P i}
      → (w : W P i) (α : Frame P w f)
      → (coh : W (Subst P // ⟪ SubstMgm P ⟫) ((i , f) , (w , α)))
      → μ-subst P (fst (μ-subst (Subst P) (W↓ (Subst P) ⟪ SubstMgm P ⟫ coh))) == (w , α)
    globularity w α coh = fst= (SubstInvar coh)

  module _ {ℓ}  {I : Type ℓ} (P : Poly I) where

    DblSlc : Poly (Ops (Subst P))
    DblSlc = Subst P // ⟪ SubstMgm P ⟫ 

    forget : (R : PolyRel P) (Ψ : SubInvar P R)
      → {i : I} {f : Op P i}
      → (w : W P i) (α : Frame P w f) (r : R (i , f) (w , α))
      → (tr : W ((P // R) // ⟪ SlcMgm P R Ψ ⟫) ((i , f) , (w , α) , r))
      → W (Subst P // ⟪ SubstMgm P ⟫) ((i , f) , (w , α))
    forget R Ψ w α r (lf .((_ , _) , (w , α) , r)) = lf ((_ , _) , w , α)
    forget R Ψ w α r (nd (((pd , β) , e) , ϕ)) = nd (((W↓ P R pd , Frame↓ P R {wαr = (w , α) , r} β) , {!!}) , {!!})

    DblSubInvar : (R : PolyRel P) (Ψ : SubInvar P R) → Type ℓ
    DblSubInvar R Ψ = {i : I} {f : Op P i}
      → (w : W P i) (α : Frame P w f) (r : R (i , f) (w , α))
      → (tr : W ((P // R) // ⟪ SlcMgm P R Ψ ⟫) ((i , f) , (w , α) , r)) 
      → Ψ (fst (μ-subst (P // R) (W↓ (P // R) ⟪ SlcMgm P R Ψ ⟫ tr))) == r 
        [ (λ x → R (i , f) x) ↓ {!!} ]

    -- So.  This second unfolding makes it clear that, individually, the data
    -- of such a witness clearly does not live in a contractible space in the
    -- case of interest.  So it must be some *combination* of such things that
    -- becomes unique somehow.

    -- But there is still this thing that I can't seem to wrap my head around:
    -- if I begin by simply slicing the trivial relation, then all the relations
    -- seem to live in a contractible space.  Whereas if I imagine starting the
    -- the first magma relation, then clearly the relation properties seem too
    -- live in a completely unbounded type.  How can both of these points of view
    -- be correct if they define the same monad structure?

    -- Here is the magma structure on the double slice.
    DblSlcMgm : PolyMagma DblSlc
    DblSlcMgm = SlcMgm (Subst P) ⟪ SubstMgm P ⟫ (SubstInvar P)

    -- Here is the magma structure on the iteration of subst
    DblSubstMgm : PolyMagma (Subst (Subst P))
    DblSubstMgm = SubstMgm (Subst P)

    know : {i : I} {f : Op P i}
      → (w : W P i) (α : Frame P w f)
      → (pd : W (Subst P) (i , f)) (β : Frame (Subst P) pd (w , α))
      → (tr : W (Subst (Subst P) // ⟪ SubstMgm (Subst P) ⟫) (((i , f) , (w , α)) , (pd , β)))
      → let (coh , ζ) = μ-subst (Subst (Subst P)) (W↓ (Subst (Subst P)) ⟪ SubstMgm (Subst P) ⟫ tr)
        in Path {A = OutFrame (Subst (Subst P)) coh}
             (μ-subst (Subst P) coh , μ-frm-subst (Subst P) coh)
             ((pd , β) , ζ)
    know w α pd β tr = SubstInvar (Subst P) tr

    wts : {i : I} {f : Op P i}
      → (w : W P i) (α : Frame P w f)
      → (pd : W (Subst P) (i , f)) (β : Frame (Subst P) pd (w , α))
      → (e : ⟪ SubstMgm P ⟫ ((i , f) , (w , α)) (pd , β))
      → (tr : W (DblSlc // ⟪ DblSlcMgm ⟫) (((i , f) , w , α) , (pd , β) , e))
      → let (coh , ζ) = μ-subst DblSlc (W↓ DblSlc ⟪ DblSlcMgm ⟫ tr)
        in Path {A = OutFrame DblSlc coh}
             (μ DblSlcMgm coh , μ-frm DblSlcMgm coh)
             (((pd , β) , e) , ζ)
    wts {i} {f} w α pd β e tr = pair= (pair= suppose {!!}) {!!}

      where suppose : μ-subst (Subst P) (W↓ (Subst P) ⟪ SubstMgm P ⟫
                              (fst (μ-subst DblSlc (W↓ DblSlc ⟪ DblSlcMgm ⟫ tr))))
                      == pd , β
            suppose = {!!}

    -- Okay, exactly.  And it looks very much like the first two guys
    -- will be more or less the same.  Hmmm.  Or maybe not.

    SimplePoly : Poly (Σ (Ops P) (W (Subst P)))
    Op SimplePoly ((i , f) , pd) = W DblSlc ((i , f) , μ-subst P pd)
    Param SimplePoly {(i , f) , pd} tr (g , pd') = Node (Subst P) pd' (g , μ-subst P pd')

    -- -- The relation induced by a magma
    -- ⟪_⟫ : ∀ {ℓ} {I : Type ℓ} {P : Poly I} (M : PolyMagma P) → PolyRel P
    -- ⟪_⟫ {P = P} M (i , f) (w , α) = Path {A = OutFrame P w}
    --   (μ M w , μ-frm M w) (f , α)

    -- claim : SubInvar DblSlc ⟪ DblSlcMgm ⟫
    -- claim {((i , f) , (w , α)) , (pd , β) , e} coh = wts w α pd β e coh

    TrplSlc : Poly (Ops DblSlc)
    TrplSlc = DblSlc // ⟪ DblSlcMgm ⟫ 

    OtherSlc : Poly (Ops (Subst (Subst P)))
    OtherSlc = Subst (Subst P) // ⟪ SubstMgm (Subst P) ⟫ 

    -- umm : TrplSlc ≃ₚ SimplePoly
    -- Sort≃ umm = equiv to from {!!} {!!}

    --   where to : Ops DblSlc → Σ (Ops P) (W (Subst P))
    --         to (((i , f) , (._ , ._)) , (pd , ._) , idp) = (i , f) , pd

    --         from : Σ (Ops P) (W (Subst P)) → Ops DblSlc
    --         from ((i , f) , pd) = ((i , f) , μ-subst P pd) , ((pd , μ-frm-subst P pd) , idp)

    -- Op≃ umm = {!!}
    -- Param≃ umm = {!!}

    -- test : Ops TrplSlc → ℕ
    -- test ((((i , f) , w , α) , (pd , β) , e₀) , (coh , ζ) , e₁) = {!!}

    -- So here is the pattern. 

    -- Oh!  So maybe this version of encode does not have all of the
    -- information that you thought!  Because in the statement below,
    -- you attempt to prove the equivalence for *any* coh.  But in the
    -- actual expansion of the statement above, coh is the collapse
    -- of a higher tree.  Could this be why you kept thinking you were
    -- off by a dimension?

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
