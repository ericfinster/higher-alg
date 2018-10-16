{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Substitution

module Slice where
  
  -- The slice polynomial
  _//_ : ∀ {ℓ} {I : Type ℓ} (P : Poly I) (M : PolyMagma P) → Poly (Ops P)
  Op (P // M) (i , f) = Σ (W P i) (λ w → μ M w == f)
  Param (P // M) {i , f} (w , e) = Node P w

  module _ {ℓ} {I : Type ℓ} (P : Poly I) (M : PolyMagma P) where
    
    slc-flatn : {i : I} {f : Op P i} → W (P // M) (i , f) → W P i
    slc-flatn-frm : {i : I} {f : Op P i} (w : W (P // M) (i , f)) → Frame P (slc-flatn w) f

    slc-flatn (lf (i , f)) = corolla P f
    slc-flatn (nd ((w , e) , κ)) = subst P w (λ g n → slc-flatn (κ g n) , slc-flatn-frm (κ g n))

    slc-flatn-frm (lf (i , f)) = corolla-frm P f
    slc-flatn-frm (nd ((w , idp) , κ)) j = μ-frm M w j ∘e
      subst-lf-eqv P w (λ g n → slc-flatn (κ g n) , slc-flatn-frm (κ g n)) j
    
    slc-bd-frame-to : {f : Ops P} (pd : W (P // M) f)
      → (g : Ops P) → Leaf (P // M) pd g → Node P (slc-flatn pd) g
    slc-bd-frame-to (lf i) ._ idp = inl idp
    slc-bd-frame-to (nd ((w , e) , κ)) g (h , n , l) = 
      subst-nd-from P w (λ g n → slc-flatn (κ g n) , slc-flatn-frm (κ g n)) g
        (h , n , slc-bd-frame-to (κ h n) g l)

    slc-bd-frame-from : {f : Ops P} (pd : W (P // M) f)
      → (g : Ops P) → Node P (slc-flatn pd) g → Leaf (P // M) pd g 
    slc-bd-frame-from (lf i) .i (inl idp) = idp
    slc-bd-frame-from (lf i) g (inr (j , p , ())) 
    slc-bd-frame-from (nd ((w , e) , κ)) g n = 
      let (h , n₀ , n₁) = subst-nd-to P w (λ g n → slc-flatn (κ g n) , slc-flatn-frm (κ g n)) g n
      in h , n₀ , slc-bd-frame-from (κ h n₀) g n₁

    postulate

      slc-bd-frame-to-from : {f : Ops P} (pd : W (P // M) f)
        → (g : Ops P) (n : Node P (slc-flatn pd) g)
        → slc-bd-frame-to pd g (slc-bd-frame-from pd g n) == n

      slc-bd-frame-from-to : {f : Ops P} (pd : W (P // M) f)
        → (g : Ops P) (l : Leaf (P // M) pd g)
        → slc-bd-frame-from pd g (slc-bd-frame-to pd g l) == l

    slc-bd-frm : {f : Ops P} (pd : W (P // M) f) 
      → (g : Ops P) → Leaf (P // M) pd g ≃ Node P (slc-flatn pd) g
    slc-bd-frm pd g = equiv (slc-bd-frame-to pd g) (slc-bd-frame-from pd g)
      (slc-bd-frame-to-from pd g) (slc-bd-frame-from-to pd g)

    -- We only need a multiplication on the equality now to finish the magma
    slc-mgm : (Ψ : {i : I} {f : Op P i} (pd : W (P // M) (i , f)) → μ M (slc-flatn pd) == f)
      → PolyMagma (P // M)
    μ (slc-mgm Ψ) pd = slc-flatn pd , Ψ pd 
    μ-frm (slc-mgm Ψ) = slc-bd-frm

  -- Now we can simply ask for the coherence multiplication in every dimension,
  -- thus using explicitly the desired frame and eliminating the need for any
  -- additional equalities.  Excellent.
  
  record CohStruct {ℓ} {I : Type ℓ} (P : Poly I) (M : PolyMagma P) : Type ℓ where
    coinductive
    field
    
      Ψ : {i : I} {f : Op P i} (pd : W (P // M) (i , f))
        → μ M (slc-flatn P M pd) == f
        
      H : CohStruct (P // M) (slc-mgm P M Ψ)

  open CohStruct

  module _ {ℓ} {I : Type ℓ} (P : Poly I) (M : PolyMagma P)
    (Ψ₀ : {i : I} {f : Op P i} (pd : W (P // M) (i , f)) → μ M (slc-flatn P M pd) == f) where

    -- So, like, these two I believe.  This is the kind of thing
    -- you've been doing for a while and looks to be quite doable
    -- just from properties of substitution.
    postulate
    
      slc-flatn₁ : {i : I} {f : Op P i}
        → {w : W P i} {e : μ M w == f}
        → (coh : W ((P // M) // slc-mgm P M Ψ₀) ((i , f) , (w , e))) 
        → slc-flatn P M (slc-flatn (P // M) (slc-mgm P M Ψ₀) coh) == w

      slc-flatn-frm₁ : {i : I} {w : W P i} 
        → (coh : W ((P // M) // slc-mgm P M Ψ₀) ((i , μ M w) , (w , idp))) 
        → slc-flatn-frm P M (slc-flatn (P // M) (slc-mgm P M Ψ₀) coh) == μ-frm M w
          [ (λ w₀ → Frame P w₀ (μ M w)) ↓ slc-flatn₁ coh ]

    next-coh : CohStruct (P // M) (slc-mgm P M Ψ₀)
    Ψ next-coh {i , f} {w , e} coh = pair= (slc-flatn₁ coh)
      (↓-app=cst-in {f = μ M {i}} {b = f} {p = slc-flatn₁ coh}
        {u = Ψ₀ (slc-flatn (P // M) (slc-mgm P M Ψ₀) coh)} {v = e} {!!})
    H next-coh = {!!}

    -- Okay, interesting.  It appears, therefore, that globularity
    -- is the only impediment to extending.  What could this possibly
    -- mean?

    -- Very, very curious.  So this seems to completely reduce the
    -- coherence question to these globular relations.

    -- Right.  And simply counting the truncation levels, it's clear
    -- that given the two previous coherences, we can finish the
    -- definition for sets: the remaining hole is a path space in
    -- a proposition and therefore contractible.  The argument will
    -- then repeat because of the truncation levels.

  module _ {ℓ} {I : Type ℓ} (P : Poly I) (M : PolyMagma P) (C : CohStruct P M) where

    Ψ₀ = Ψ C
    Ψ₁ = Ψ (H C)

    blorp : {i : I} {f : Op P i}
      → {w : W P i} {e : μ M w == f}
      → (coh : W ((P // M) // slc-mgm P M Ψ₀) ((i , f) , (w , e))) 
      → slc-flatn P M (slc-flatn (P // M) (slc-mgm P M Ψ₀) coh) == w
    blorp coh = fst= (Ψ₁ coh)

    bleep : {i : I} {f : Op P i}
      → {w : W P i} {e : μ M w == f}
      → (coh : W ((P // M) // slc-mgm P M Ψ₀) ((i , f) , (w , e))) 
      → Ψ₀ (slc-flatn (P // M) (slc-mgm P M Ψ₀) coh)
        == ap (μ M) (blorp coh) ∙ e
    bleep {i} {f} {w} {e} coh = ↓-app=cst-out (snd= (Ψ₁ coh))

  -- Crazy!  So the above shows that globularity is a *consequence* of the definition.
  -- So that is extremely reassuring.  And there's going to be whole families of
  -- similar relations that I can derive just from chopping up the iterated
  -- path overs in the correct ways.

  -- Fantastic.  So this leaves very little doubt in my head that the
  -- definition is correct.

  -- I mean, this is the main thing you were still worried about: that the
  -- underlying "opetopic type" was not coherent and that therefore you
  -- wouldn't be able to prove the higher coherences.  But this seems to
  -- be completely settled with the above observation: the globularity
  -- relations are a *consequence* of the above definition.

  -- And the previous section seems to show that they are the only
  -- obstruction to lifting the coherence to the next step.

  -- This strongly suggests to me that there should be some kind of
  -- "configuration" of identities which is self-perpetuating, just
  -- like in the case of equivalences.  Remains just to find them...

  -- module _ {ℓ} {I : Type ℓ} (P : Poly I) where

  --   flatn-slc-flatn : {i : I} {f : Op P i}
  --     → {w : W P i} {α : Frame P w f}
  --     → (coh : W (Subst P // subst-mgm P) ((i , f) , w , α)) 
  --     → flatn P (slc-flatn (Subst P) (subst-mgm P) coh) == w
  --   flatn-slc-flatn = {!!}

  --   flatn-frm-slc-flatn : {i : I} {f : Op P i}
  --     → {w : W P i} {α : Frame P w f}
  --     → (coh : W (Subst P // subst-mgm P) ((i , f) , w , α))
  --     → flatn-frm P (slc-flatn (Subst P) (subst-mgm P) coh) == α [ (λ w → Frame P w f) ↓ flatn-slc-flatn coh ]
  --   flatn-frm-slc-flatn coh = {!!}
    
  --   subst-coh : CohStruct (Subst P) (subst-mgm P)
  --   Ψ subst-coh {i , f} {w , α} coh =
  --     pair= (flatn-slc-flatn coh) (flatn-frm-slc-flatn coh)
  --   H subst-coh = {!!}

