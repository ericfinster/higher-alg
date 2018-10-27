{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import WPaths

module Node {ℓ} {I : Type ℓ} (P : Poly I) where

  -- The height of a node
  height : {i : I} (w : W P i)
    → (g : Ops P) (n : Node P w g) → ℕ
  height (lf i) g (lift ())
  height (nd (f , ϕ)) .(_ , f) (inl idp) = 0
  height (nd (f , ϕ)) g (inr (k , p , n)) = S (height (ϕ k p) g n)

  -- We can extract a decoration given a node
  node-dec : {i : I} (w : W P i)
    → {j : I} (g : Op P j) 
    → Node P w (j , g)
    → Decor P g (W P)
  node-dec (lf i) g (lift ())
  node-dec (nd (f , ϕ)) .f (inl idp) = ϕ
  node-dec (nd (f , ϕ)) g (inr (k , p , n)) = node-dec (ϕ k p) g n

  -- Now, given a node of height 0, we want to
  -- claim that the tree is determined.
  node-recon : {i : I} (w : W P i)
    → {j : I} (f : Op P j)
    → (n : Node P w (j , f))
    → (is-base : height w (j , f) n == 0)
    → w == {!!}
  node-recon = {!!}
  -- node-recon (lf i) f (lift ()) is-b
  -- node-recon (nd (f , ϕ)) f₀ (inl x) is-b = {!!}
  -- node-recon (nd (f , ϕ)) f₀ (inr x) is-b = {!!}

  is-height-preserving : {i j : I} (w₀ : W P i) (w₁ : W P j)
    → (ν : (g : Ops P) → Node P w₀ g ≃ Node P w₁ g) → Type ℓ
  is-height-preserving w₀ w₁ ν = (g : Ops P) (n : Node P w₀ g)
    → height w₀ g n == height w₁ g (–> (ν g) n)

  -- Is there a different way to phrase the equivalence
  -- of nodes so that this duplication doesn't happen?
  nd-eqv : {i : I} (w₀ w₁ : W P i) → Type ℓ
  nd-eqv w₀ w₁ = (j : I) → Σ (Op P j) (λ g → Node P w₀ (j , g)) ≃ Σ (Op P j) (λ g → Node P w₁ (j , g))

  -- What about this?  No, this can't be right.

  conj : {i j : I} (w₀ : W P i) (w₁ : W P j)
    → (ν : (g : Ops P) → Node P w₀ g ≃ Node P w₁ g) 
    → (is-h : is-height-preserving w₀ w₁ ν)
    → (i , w₀) == (j , w₁)
  conj (lf i) (lf j) ν is-h = {!!} -- Shit.
  conj (lf i) (nd (g , ψ)) ν is-h = {!!}  -- not possible
  conj (nd (f , ϕ)) (lf j) ν is-h = {!!}  -- not possible
  conj (nd (f , ϕ)) (nd (g , ψ)) ν is-h with (–> (ν (_ , f)) (inl idp))
  conj (nd (f , ϕ)) (nd (.f , ψ)) ν is-h | inl idp = pair= idp (ap (λ x → nd (f , x)) {!!})

    where lem : (k : I) (p : Param P f k) → ϕ k p == ψ k p
          lem k p = {!!}

  conj (nd (f , ϕ)) (nd (g , ψ)) ν is-h | inr x = {!!} -- not possible because of height


  
  
