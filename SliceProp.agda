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

  module _ {ℓ} {I : Type ℓ} (P : Poly I) (M : PolyMagma P) where

    lf-height : {i : I} {f : Op P i} (pd : W (P // M) (i , f))
      → (g : Ops P) (l : Leaf (P // M) pd g) → ℕ
    lf-height (lf (i , f)) g l = 0
    lf-height (nd ((w , e) , κ)) g (h , n , l) = height P w h n
    
    is-good : {i : I} {f : Op P i} (pd : W (P // M) (i , f))
      (w : Op (P // M) (i , f)) (β : Frame (P // M) pd w)
      → Type ℓ
    is-good pd (w , e) β = (v : Ops (P // M)) (n : Node (P // M) pd v)
      → (g : Ops P) (l : Leaf (P // M) (subtree (P // M) pd (snd v) n) g)
      → (lf-height (subtree (P // M) pd (snd v) n) g l) ≤
        (height P w g (–> (β g) (subtree-lf-to (P // M) pd (snd v) n g l)))

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
    -- leaf-height : {i : I} {f : Op P i}
    --   → (pd : W (Subst P) (i , f))
    --   → (g : Ops P) (l : Leaf (Subst P) pd g) → ℕ
    -- leaf-height (lf (i , f)) g l = 0
    -- leaf-height (nd ((w , α) , κ)) g (h , n , l) = height P w h n

    -- -- Okay.  This was the original idea.  This says that the
    -- -- frame β uniformly preserves the ordering.  Will this be enough?
    -- is-good : {i : Ops (Subst P)} → Op SubstSubst i → Type ℓ
    -- is-good {(i , f) , w , α} (pd , β) = (v : Ops (Subst P)) (n : Node (Subst P) pd v)
    --   → (g : Ops P) (l : Leaf (Subst P) (subtree (Subst P) pd (snd v) n) g)
    --   → (leaf-height (subtree (Subst P) pd (snd v) n) g l) ≤
    --     (height P w g (–> (β g) (subtree-lf-to (Subst P) pd (snd v) n g l)))

    -- μ-slc : {σ : Ops (Subst P)} → W SlcSubst σ → Op SlcSubst σ
    -- μ-slc {(i , f) , (w , α)} coh = {!flatn (Subst P)!} , {!!}

  -- subst-mgm : PolyMagma Subst
  -- PolyMagma.μ subst-mgm w = flatn w , flatn-frm w
  -- PolyMagma.μ-frm subst-mgm w = bd-frm w


    -- μ-bd : {pd : Ops (Subst P)} → W BD pd → Op BD pd
    -- μ-bd {(i , f) , (w , α)} coh = flatn₁ coh ,
    --   pair= (flatn-flatn w α coh) (flatn-frm-flatn w α coh)

    -- -- So, here is the uniqueness conjecture:
    -- -- (Well, part of it. you'll also need the compatibility with the frame ...)

    -- conj : {w : Ops (Subst P)} (coh : W BD w)
    --   → (pd : Op BD w) (β : Frame BD coh pd)
    --   → pd == μ-bd coh
    -- conj {(i , f) , ._} (lf ._) (lf ._ , idp) β = {!β ((i , f) , nd (f , (λ j p → lf j)) , corolla-frm P f)!}
    --   -- Exactly, this case is solvable by contradiction ...
    -- conj {(i , f) , ._} (lf ._) (nd ((w , α) , δ) , idp) β = pair= (ap nd {!!}) {!!}
    --   -- Wow, okay.  And this in fact looks doable.  You're going to show that
    --   -- δ must be the trivial decoration, and then inside the node constructor, 
    --   -- you'll use the subst-unit coherence to finish the job.
    -- conj {(i , f) , _} (nd ((pd₀ , e₀) , κ)) (pd₁ , idp) β = pair= {!!} {!!}

    -- Hmmm.  This did not come out as I wanted it to.
    -- I seem to be off by a dimension or something.
    -- What did I do wrong?
    -- reconstruct-tr : {i : I} {f : Op P i}
    --   → (w : W P i) (α : Frame P w f)
    --   → (pd : W (Subst P) (i , f))
    --   → (β : Frame (Subst P) pd (w , α))
    --   → (is-g : is-good {(i , f) , w , α} (pd , β))
    --   → flatn P pd == w
    -- reconstruct-tr w α (lf (i , f)) β is-g = {!!}
    -- reconstruct-tr w α (nd ((w₀ , α₀) , κ)) β is-g = {!!}

    -- reconstruct : {i : Ops (Subst P)} (pd : Op SubstSubst i) (is-g : is-good {i = i} pd)
    --   → hfiber (forgetful {i = i}) pd
    -- reconstruct {(i , f) , w , α} (pd , β) is-g = (pd , {!!}) , {!!}

    -- Okay, and to finish here, we need to know that the slice
    -- of the substitution has a multiplication.
    reconstruct-tr : {i : I} {f : Op P i}
      → (w : W P i) (α : Frame P w f)
      → (coh : W (Subst P // subst-mgm P) ((i , f) , w , α))
      → (pd : Op (Subst P // subst-mgm P) ((i , f) , w , α))
      → (β : Frame (Subst P // subst-mgm P) coh pd)
      → (is-g : is-good (Subst P) (subst-mgm P) coh pd β)
      → Type ℓ
    reconstruct-tr = {!!}
