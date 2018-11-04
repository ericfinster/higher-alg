{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Substitution
open import WPaths
open import PolyMonad

module wip.Rigidity {ℓ} {I : Type ℓ} {P : Poly I} (M : PolyMagma P) where

  postulate

    Ψ₀ : CohWit M
    Ψ₁ : CohWit (SlcMgm Ψ₀)

  P₀ = P
  P₁ = P // M
  P₂ = (P // M) // SlcMgm Ψ₀

  -- So, my idea is to do this in complete generality.
  -- I think you will need the completely general statement
  -- Anyway, so why not try to write out what you think it
  -- should say and see what happens?

  rigidity : {i : I} {f : Op P i}
    → (w : W P i) (e : μ M w == f) 
    → (coh : W P₂ ((i , f) , (w , e)))
    → (α : μ (SlcMgm Ψ₁) coh == μ (SlcMgm Ψ₁) coh)
    → (j : I) (g : Op P j) (v : W P j) (r : μ M v == g) 
    → (n : Node P₁ (fst (μ (SlcMgm Ψ₁) coh)) (((j , g) , v , r)))
    → r == r
  rigidity w e coh α = {!fst (μ (SlcMgm Ψ₁) coh)!}

  -- Okay, there it is.  That's your claim.
  -- Moreover, there should be a map in the other direction
  -- as well which is essentially trivial (just ap the equality
  -- everywhere).  

  -- In fact, I expect that something like this should be an
  -- eqivalence.  However, in order to get the coherence you
  -- are looking for, I think it should suffice to show that
  -- it is a retraction.
  

  -- postulate

  --   Ψ : CohWit (Subst P) (subst-mgm P)

  -- SlcSubst : Poly (Ops (Subst P))
  -- SlcSubst = Subst P // subst-mgm P

  -- SlcMgm : PolyMagma SlcSubst
  -- SlcMgm = slc-mgm (Subst P) (subst-mgm P) Ψ

  -- -- Okay, so we suppose we have proven the associativity
  -- -- and so on for the slice which results in the coherence
  -- -- witness above by general principles.  Now I think we
  -- -- can state the main idea:

  -- rigidity : {i : I} {f : Op P i}
  --   → (w : W P i) (α : Frame P w f)
  --   → (coh : W SlcSubst ((i , f) , (w , α)))
  --   → (e : μ SlcMgm coh == μ SlcMgm coh)
  --   → e == idp
  -- rigidity {i} {f} w α (lf .((i , f) , w , α)) e = {!e!}

  --   where lem : idp == ap (λ z → flatn P z , flatn-frm P z) (fst= e)
  --         lem = anti-whisker-right (snd (μ SlcMgm (lf ((i , f) , w , α))))
  --                 (↓-app=cst-out (snd= e))
          
  -- rigidity {i} .(flatn P pd) .(flatn-frm P pd) (nd ((pd , idp) , θ)) e =
  --   {!↓-app=cst-out (snd= e)!}

  -- Okay.  So we see indeed that this is significantly different
  -- from what you were trying to prove before.

  -- So, the first thing we have to show is that any
  -- automorphism of this corolla:
  -- 
  -- nd ((w , α) , (λ j p → lf j)) , Ψ (lf ((i , f) , w , α))
  --
  -- which preserves the proof that multiplication in the
  -- slice is w must in fact be the identity.
  --

  -- So, what's quite fantastic about that is that this is
  -- something extremely concrete that you can check by hand.
  -- And it sounds extremely plausible!!

  -- And now in the second case, we have to prove that
  -- automorphisms of

  -- subst (Subst P) pd (λ g n →
  --    slc-flatn (Subst P) (subst-mgm P) (θ g n) ,
  --    slc-flatn-frm (Subst P) (subst-mgm P) (θ g n))
  --  , Ψ (nd ((pd , idp) , θ))

  -- preserving the laws are also trivial.

