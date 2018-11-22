{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Substitution
open import PolyMonad

module wip.Lifting where

  Ext : ∀ {ℓ} {I : Type ℓ} {P : Poly I} (R : PolyRel P) → Type (lsucc ℓ)
  Ext {ℓ} {P = P} R = {f : Ops P} (α : InFrame P f) → R f α → Type ℓ

  ΣE : ∀ {ℓ} {I : Type ℓ} {P : Poly I} {R : PolyRel P} (E : Ext R) → PolyRel P
  ΣE {R = R} E f α = Σ (R f α) (E α)

  module _ {ℓ} {I : Type ℓ} {P : Poly I} {R : PolyRel P} (E : Ext R) where

    w-fst : {f : Ops P} → W (P // ΣE E) f → W (P // R) f
    w-fst (lf (i , f)) = lf (i , f)
    w-fst {i , f} (nd (((w , α) , (r , e)) , κ)) =
      nd (((w , α) , r) , λ g n → w-fst (κ g n))

    postulate

      -- This is clear, since substitution does not use the relation element...
      w-fst-coh : {f : Ops P} (pd : W (P // ΣE E) f)
        → Path {A = InFrame P f} (flatn R (w-fst pd) , flatn-frm R (w-fst pd))
                                 (flatn (ΣE E) pd , flatn-frm (ΣE E) pd)

      -- And, of course, this will work for the baez-dolan frame as well.

      -- But the thing is, there is a whole infinite family of these projection
      -- operations.  And you have to understand the special thing that happens
      -- when the tower is *applied to itself*.
      
    ExtInvar : SubInvar R → Type ℓ
    ExtInvar Ψ = {f : Ops P} (pd : W (P // ΣE E) f)
      → E (flatn R (w-fst pd) , flatn-frm R (w-fst pd)) (Ψ (w-fst pd))

    ΣEInvar : (Ψ : SubInvar R) → ExtInvar Ψ → SubInvar (ΣE E)
    ΣEInvar ΨR ΨE {f} pd = transport (ΣE E f) (w-fst-coh pd) (ΨR (w-fst pd) , ΨE pd)

    SlcInvar : (ΨR : SubInvar R) (ΨE : ExtInvar ΨR)
      → SubInvar ⟪ SlcMgm ΨR ⟫ 
      → SubInvar ⟪ SlcMgm (ΣEInvar ΨR ΨE) ⟫ 
    SlcInvar ΨR ΨE SM {(i , f) , (w , α) , r , e} coh = {!!}

      -- Okay, so the first part should come from some kind
      -- of erasure result and the assumption that R extends
      -- to the slice.  Similarly for the last one.

      -- For the middle one, you'll get the path over r from
      -- again erasure and the hypothesis on R.  The final
      -- piece, then is a path over of the form bleep == e.
      
      -- This one I don't see.  You could certainly add it to
      -- the hypotheses on E, but then this starts to look like
      -- something that will unwind on you.

      -- At some point, you have to find out why this process
      -- terminates ....

      -- (Note this could be a special property of substitution ....)

      where blorp : SubInvar (ΣE E)
            blorp = ΣEInvar ΨR ΨE

            bloop : W (P // ΣE E) (i , f)
            bloop = flatn ⟪ SlcMgm blorp ⟫ coh

            bleep : ΣE E (i , f) (flatn (ΣE E) bloop ,
                                  flatn-frm (ΣE E) bloop)
            bleep = blorp bloop

            blomp : R (i , f) (flatn R (w-fst bloop) , flatn-frm R (w-fst bloop))
            blomp = ΨR (w-fst bloop)

  CohLift : ∀ {ℓ} {I : Type ℓ} {P : Poly I} (M : PolyMagma P) (C : CohStruct M)
    → (E : Ext ⟪ M ⟫) (ΨE : ExtInvar E (Ψ C))
    → CohStruct (SlcMgm (ΣEInvar E (Ψ C) ΨE))
  Ψ (CohLift {P = P} M C E ΨE) = SlcInvar E (Ψ C) ΨE (Ψ (H C))
  H (CohLift M C E ΨE) = {!H C!}

  -- Yeah, so it still remains slightly asymmetric.  You don't have this
  -- have that the summed structure is also that of a magma.

    -- Okay, with this setup, things feel more symmetric.
    -- But do we have the right kind of structure to repeat?

  -- module _ {ℓ} {I : Type ℓ} (P : Poly I) (R : PolyRel P) where

  --   -- Okay, in this section, I want to think about
  --   -- how one extends coherence structures over extensions
  --   -- of a relation

  --   postulate

  --     Ψ₀ : SubInvar R
  --     H₀ : CohStruct (SlcMgm Ψ₀)
  --     E : {f : Ops P} (α : InFrame P f) → R f α → Type ℓ

  --   ΣE : PolyRel P
  --   ΣE f α = Σ (R f α) (E α)

  --   -- Now what?
  --   postulate

  --     erase : {f : Ops P} → W (P // ΣE) f → W (P // R) f

  --     E-invar : {f : Ops P} (pd : W (P // ΣE) f)
  --       → E (flatn R (erase pd) , flatn-frm R (erase pd)) (Ψ₀ (erase pd))

  --     -- This is clear, since substitution does not use the
  --     -- relation element...
  --     flatn-compat : {f : Ops P} (pd : W (P // ΣE) f)
  --       → Path {A = InFrame P f} (flatn R (erase pd) , flatn-frm R (erase pd))
  --                                (flatn ΣE pd , flatn-frm ΣE pd)

  --   ΨE : SubInvar ΣE
  --   ΨE {f} pd = transport (ΣE f) (flatn-compat pd) (Ψ₀ (erase pd) , E-invar pd)

  --   -- -- An invariant relation induces a magma
  --   -- SlcMgm : ∀ {ℓ} {I : Type ℓ} {P : Poly I} {R : PolyRel P}
  --   --   → SubInvar R → PolyMagma (P // R)
  --   -- μ (SlcMgm {R = R} Ψ) pd = (flatn R pd , flatn-frm R pd) , Ψ pd
  --   -- μ-frm (SlcMgm {R = R} Ψ) pd = bd-frm R pd

  --   -- -- The relation induced by a magma
  --   -- MgmRel : ∀ {ℓ} {I : Type ℓ} {P : Poly I} (M : PolyMagma P) → PolyRel P
  --   -- MgmRel {P = P} M (i , f) (w , α) = Path {A = OutFrame P w}
  --   --   (μ M w , μ-frm M w) (f , α)

  --   -- So, how do we complete the process of pulling this guy back
  --   -- in higher dimensions?  Something like: the magma relation for
  --   -- ΨE is equivalent to the sum of a magma relation for Ψ₀ plus
  --   -- some compatibility data, which one can see as an extension.

  --   SlcRel : PolyRel (P // R)
  --   SlcRel ((i , f) , (w , α) , r) (pd , β) =
  --     Path {A = OutFrame (P // R) pd}
  --       (((flatn R pd , flatn-frm R pd) , Ψ₀ pd) , bd-frm R pd)
  --       (((w , α) , r) , β)

  --   -- Okay, so that's the the unfolding of MgmRel (SlcMgm Ψ₀).
  --   -- Right, so the first step is to show that you can erase
  --   -- everything down to get a coherence relation in R.

  --   -- Then you're going to apply Ψ H₀ to the result, given a
  --   -- path of the above type.  Indeed, 
    
  --   -- So then here is where we have some work to do.
  --   HE : CohStruct (SlcMgm ΨE)
  --   Ψ HE {(i , f) , (w , α) , (r , e)} coh = {!Ψ H₀ !}
  --   H HE = {!!}
