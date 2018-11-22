{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Substitution
open import PolyMonad

module wip.Expanding {ℓ} {I : Type ℓ} (P : Poly I) where

  -- I want to write out explicitly the first couple of
  -- expansions of what I need to prove in order to show
  -- that substitution is a monad.  I think you need to
  -- stare at it in order to understand how it might work.

  TR : PolyRel P
  TR _ _ = Lift ⊤

  SubstInv : SubInvar TR
  SubstInv _ = lift tt

  SubstPoly : Poly (Ops P)
  SubstPoly = P // TR

  SubstMgm : PolyMagma SubstPoly
  μ SubstMgm pd = (flatn TR pd , flatn-frm TR pd) , lift tt
  μ-frm SubstMgm pd = bd-frm TR pd

  -- Okay, there's the magma.  Now what?

  SInv₁ : SubInvar ⟪ SubstMgm ⟫
  SInv₁ {(i , f) , ((w , α) , lift tt)} coh = res
  
    where res : (((flatn TR (flatn ⟪ SubstMgm ⟫ coh) , flatn-frm TR (flatn ⟪ SubstMgm ⟫ coh)) , lift tt) , bd-frm TR (flatn ⟪ SubstMgm ⟫ coh)) ==
                (((w , α) , lift tt) , flatn-frm ⟪ SubstMgm ⟫ coh)
          res = {!!}

  SInv₂ : SubInvar ⟪ SubstMgm ⇙ SInv₁ ⟫
  SInv₂ {((i , f) , ((w , α) , lift tt)) , ((pd , β) , e)} trp = res

    where res : (((flatn ⟪ SubstMgm ⟫ (flatn ⟪ SubstMgm ⇙ SInv₁ ⟫ trp) , flatn-frm ⟪ SubstMgm ⟫ (flatn ⟪ SubstMgm ⇙ SInv₁ ⟫ trp)) , SInv₁ (flatn ⟪ SubstMgm ⇙ SInv₁ ⟫ trp)) ,
                         bd-frm ⟪ SubstMgm ⟫ (flatn ⟪ SubstMgm ⇙ SInv₁ ⟫ trp))  ==
                (((pd , β) , e) , flatn-frm ⟪ SubstMgm ⇙ SInv₁ ⟫ trp)
          res = {!fst= (fst= (fst= e))!}

  -- Okay, so : WHERE'S THE COHERENCE?!?!?
  -- Note that it appears we can in fact match on e.
  -- This *must* be some kind of source of coherence.
  -- What does it accomplish?

  SInv₂' : SubInvar ⟪ SubstMgm ⇙ SInv₁ ⟫
  SInv₂' {((i , f) , ((.(flatn TR pd) , .(flatn-frm TR pd)) , lift tt)) , ((pd , .(bd-frm TR pd)) , idp)} trp = res

    where res : (((flatn ⟪ SubstMgm ⟫ (flatn ⟪ SubstMgm ⇙ SInv₁ ⟫ trp) , flatn-frm ⟪ SubstMgm ⟫ (flatn ⟪ SubstMgm ⇙ SInv₁ ⟫ trp)) , SInv₁ (flatn ⟪ SubstMgm ⇙ SInv₁ ⟫ trp)) ,
                         bd-frm ⟪ SubstMgm ⟫ (flatn ⟪ SubstMgm ⇙ SInv₁ ⟫ trp))  ==
                (((pd , _) , idp) , flatn-frm ⟪ SubstMgm ⇙ SInv₁ ⟫ trp)
          res = {!pd!}

  -- And now, what is the strategy to prove this?
  -- I think I know what it is:  The idea is to say that
  -- this identity *has already been proven* as we can obtain
  -- it by:
  --
  --   1) Iteratively erasing the additional information from trp
  --   2) Observing that we can then write this as a flatten in the
  --      trivial relation one dimension higher
  --   3) Observing that there is a path between these two guys.
  --   4) Composing with coherences to fix up the types on the two ends.
  --

  -- Right, so the thing that happens when you math is that the
  -- (w , α) in SInv₁ becomes (flatn TR pd , flatn-frm TR pd) so
  -- that the first factor "looks like" it should be the ap of
  -- flatn to some (dependent?) path.

  -- Okay, I actually think this will work.  The central theme is that
  -- you can derive 2-associativity from pulling back the fact that you
  -- know 1-associativity *globally*, that is, for all substitution
  -- monads.

  -- So of course, it seems completely natural that this kind of pattern
  -- continues.  If I can trade 1-associativity globally for 2-associativity
  -- locally, then I should be able to go as high as I like with this
  -- method.

  -- But what I don't quite see is the form of this argument which
  -- let's you *iterate* it indefinately.  That is, the above argument
  -- (in dimension 2) will amount to finding some finite list of equations
  -- to prove.  But how do I see that this finite set *suffices* to iterate
  -- in all remaining dimensions?
