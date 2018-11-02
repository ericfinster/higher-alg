{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import WPaths
open import Substitution
open import PolyMonad
open import TreeLemmas

module Reconstruction where

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


  module _ {ℓ} {I : Type ℓ} (P : Poly I) (M : PolyMagma P)
    (Ψ₀ : CohWit P M) (Ψ₁ : CohWit (P // M) (slc-mgm P M Ψ₀)) where

    P₀ = P
    P₁ = P // M
    P₂ = (P // M) // (slc-mgm P M Ψ₀)

    M₀ = M
    M₁ = slc-mgm P M Ψ₀
    M₂ = slc-mgm (P // M₀) M₁ Ψ₁

    recons : {w : Ops P₁} (coh : W P₂ w)
      → (pd : Op P₂ w) (β : Frame P₂ coh pd) (is-g : is-good P₁ M₁ coh pd β)
      → μ M₂ coh == pd
    recons (lf ((i , f) , w , e)) (lf .(i , f) , ω) β is-g = {!!}
    recons (lf ((i , ._) , ._)) (nd ((w₀ , idp) , κ) , idp) β is-g =
      pair= (<– (W=-equiv (P // M)) (pair= (pair= {!–> (β ((i , μ M w₀) , ?)) idp!} {!!}) {!!})) {!!}
    recons {(i , f) , w , e} (nd ((x , y) , ρ)) (pd , ω) β is-g = {!!}

    -- Yikes!

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
