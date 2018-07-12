{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Inspect

module Poly where

  record Poly (I : Type₀) : Type₁ where
    field
      γ : I → Type₀
      ρ : (i : I) (c : γ i) → Type₀
      τ : (i : I) (c : γ i) (p : ρ i c) → I

  open Poly public
  
  ⟦_⟧ : {I : Type₀} (P : Poly I) → (I → Set) → I → Set
  ⟦ P ⟧ X i = Σ (γ P i) (λ c → (p : ρ P i c) → X (τ P i c p))

  module _ {I : Type₀} (P : Poly I) where
  
    data W : I → Type₀ where
      lf : (i : I) → W i
      nd : (i : I) → ⟦ P ⟧ W i → W i

    leaf : {i : I} → W i → Type₀
    leaf (lf i) = ⊤
    leaf (nd i (c , δ)) = Σ (ρ P i c) (leaf ∘ δ)

    leaf-type : {i : I} (w : W i) (l : leaf w) → I
    leaf-type (lf i) tt = i
    leaf-type (nd i (c , δ)) (p , l) = leaf-type (δ p) l
    
    node : {i : I} → W i → Type₀
    node (lf i) = ⊥
    node (nd i (c , δ)) = ⊤ ⊔ Σ (ρ P i c) (node ∘ δ) 

    node-type : {i : I} (w : W i) (n : node w) → Σ I (γ P)
    node-type (lf i) ()
    node-type (nd i (c , δ)) (inl unit) = i , c
    node-type (nd i (c , δ)) (inr (p , n)) = node-type (δ p) n

  module _ {I : Type₀} (P : Poly I) where
  
    γ-fr : I → Type₀
    γ-fr = W P

    ρ-fr : (i : I) → γ-fr i → Type₀
    ρ-fr i (lf .i) = ⊤
    ρ-fr i (nd .i (c , δ)) = Σ (ρ P i c) (λ p → ρ-fr (τ P i c p) (δ p))

    τ-fr : (i : I) (c : γ-fr i) → ρ-fr i c → I
    τ-fr i (lf .i) unit = i
    τ-fr i (nd .i (c , δ)) (p₀ , p₁) = τ-fr (τ P i c p₀) (δ p₀) p₁

    η-fr : (i : I) → γ-fr i
    η-fr = lf

    ηρ-contr-fr : (i : I) → is-contr (ρ-fr i (η-fr i))
    ηρ-contr-fr i = Unit-level

    μ-fr : (i : I) (c : γ-fr i) (δ : (p : ρ-fr i c) → γ-fr (τ-fr i c p)) → γ-fr i
    μ-fr i (lf .i) δ = δ unit
    μ-fr i (nd .i (c , δ₀)) δ = nd i (c , λ p₀ → μ-fr (τ P i c p₀) (δ₀ p₀) (λ p₁ → δ (p₀ , p₁)))

    μρ-to-fr : (i : I) (w : W P i)
      → (δ : (p : ρ-fr i w) → W P (τ-fr i w p))
      → Σ (ρ-fr i w) (λ p → ρ-fr (τ-fr i w p ) (δ p))
      → ρ-fr i (μ-fr i w δ)
    μρ-to-fr i (lf .i) δ (unit , p₁) = p₁
    μρ-to-fr i (nd .i (c , δ₀)) δ ((p₀ , p₁) , p₂) = p₀ , μρ-to-fr (τ P i c p₀) (δ₀ p₀) (λ p₃ → δ (p₀ , p₃)) (p₁ , p₂)

    μρ-from-fr : (i : I) (w : W P i)
      → (δ : (p : ρ-fr i w) → W P (τ-fr i w p))
      → ρ-fr i (μ-fr i w δ)
      → Σ (ρ-fr i w) (λ p → ρ-fr (τ-fr i w p) (δ p))
    μρ-from-fr i (lf .i) δ p = unit , p
    μρ-from-fr i (nd .i (c , δ₀)) δ (p₀ , p₁) =
      let pp = μρ-from-fr (τ P i c p₀) (δ₀ p₀) (λ p₂ → δ (p₀ , p₂)) p₁
      in (p₀ , fst pp) , snd pp

    μρ-to-from-fr : (i : I) (w : W P i)
      → (δ : (p : ρ-fr i w) → W P (τ-fr i w p))
      → (p : ρ-fr i (μ-fr i w δ))
      → μρ-to-fr i w δ (μρ-from-fr i w δ p) == p
    μρ-to-from-fr i (lf .i) δ p = idp
    μρ-to-from-fr i (nd .i (c , δ₀)) δ (p₀ , p₁) = 
      let ih = μρ-to-from-fr (τ P i c p₀) (δ₀ p₀) (λ p₂ → δ (p₀ , p₂)) p₁
      in ap (λ p₂ → p₀ , p₂) ih

    μρ-from-to-fr : (i : I) (w : W P i)
      → (δ : (p : ρ-fr i w) → W P (τ-fr i w p))
      → (p : Σ (ρ-fr i w) (λ p → ρ-fr (τ-fr i w p ) (δ p)))
      → μρ-from-fr i w δ (μρ-to-fr i w δ p) == p
    μρ-from-to-fr i (lf .i) δ (unit , p₁) = idp
    μρ-from-to-fr i (nd .i (c , δ₀)) δ ((p₀ , p₁) , p₂) =
      let ih = μρ-from-to-fr (τ P i c p₀) (δ₀ p₀) (λ p₃ → δ (p₀ , p₃)) (p₁ , p₂)
          ρ-fr-δ x = ρ-fr (τ-fr (τ P i c (fst x)) (δ₀ (fst x)) (snd x)) (δ x)
      in pair= (pair= idp (fst= ih)) (↓-ap-in ρ-fr-δ (λ x → (p₀ , x)) (snd= ih))

    μρ-equiv-fr : (i : I) (w : W P i)
      → (δ : (p : ρ-fr i w) → W P (τ-fr i w p))
      → Σ (ρ-fr i w) (λ p → ρ-fr (τ-fr i w p ) (δ p))
        ≃' ρ-fr i (μ-fr i w δ)
    μρ-equiv-fr i w δ =
      equiv' (μρ-to-fr i w δ) (μρ-from-fr i w δ)
             (μρ-to-from-fr i w δ) (μρ-from-to-fr i w δ)

  ZeroPoly : (I : Type₀) → Poly I
  γ  (ZeroPoly I) i = ⊥
  ρ (ZeroPoly I) i () 
  τ (ZeroPoly I) i () _
