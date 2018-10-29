{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import WPaths
open import Substitution
open import PolyMonad

module SliceProp where

  --
  -- An attempt to show that the inclusion
  --
  --   Slice (Subst P) --> Subst (Subst P)
  --
  -- is monic which (more or less) implies the coherent
  -- structure on the universe.
  --


  module _ {ℓ} {I : Type ℓ} (P : Poly I) where

    SlcSubst : Poly (Σ (Σ I (Op P)) (Op (Subst P)))
    SlcSubst = Subst P // subst-mgm P
      
    SubstSubst : Poly (Σ (Σ I (Op P)) (Op (Subst P)))
    SubstSubst = Subst (Subst P)

    forgetful : {i : Ops (Subst P)} → Op SlcSubst i → Op SubstSubst i
    forgetful {(i , f) , ._ , ._} (pd , idp) = pd , bd-frm P pd

    -- So, our strategy is to show that the homotopy fibers
    -- of this map are equivalent to the proposition that
    -- the given frame is "everywhere order preserving"

    is-good : {i : Ops (Subst P)} → Op SubstSubst i → Type ℓ
    is-good (pd , β) = {!!}

    -- Okay, so this notion will need a bit of preparation....

  -- Right.  Just need a bit of machinery for determining the
  -- ordering on leaves of the pasting diagram and so on.
  -- This kind of thing should not be so difficult.

  -- So, looking ahead, how are you going to decompose the
  -- tree using the information about the preservation of
  -- order?

  -- Right, this is not hard: given any binary function on
  -- the nodes of a tree, we should be able to decompose
  -- it into a subtree of those nodes which are assigned one
  -- and the rest in such a way that the tree is in fact
  -- just the graft of the lower with the induced decoration.

  -- So, it seems to me we will be able to recover the tree
  -- and frame one dimension down.  But then to complete the
  -- proof, we have to show that we also recover the frame
  -- β.  This part I do not immediately see how to do.  But okay,
  -- maybe it will become more clear as you go.

  -- Yeah, just a bit worried about the equivalence with
  -- the frame.  Will something come to save you?
