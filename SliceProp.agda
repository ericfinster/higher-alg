{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import WPaths
open import Substitution
open import PolyMonad
open import TreeLemmas

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

    -- we assign a height to each leaf using the height
    -- of the node that it lives over
    leaf-height : {i : I} {f : Op P i}
      → (pd : W (Subst P) (i , f))
      → (g : Ops P) (l : Leaf (Subst P) pd g) → ℕ
    leaf-height (lf (i , f)) g l = 0
    leaf-height (nd ((w , α) , κ)) g (h , n , l) = height P w h n

    -- Okay.  This was the original idea.  This says that the
    -- frame β uniformly preserves the ordering.  Will this be enough?
    is-good : {i : Ops (Subst P)} → Op SubstSubst i → Type ℓ
    is-good {(i , f) , w , α} (pd , β) = (v : Ops (Subst P)) (n : Node (Subst P) pd v)
      → (g : Ops P) (l : Leaf (Subst P) (subtree (Subst P) pd (snd v) n) g)
      → (leaf-height (subtree (Subst P) pd (snd v) n) g l) ≤
        (height P w g (–> (β g) (subtree-lf-to (Subst P) pd (snd v) n g l)))


