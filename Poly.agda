{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module Poly where

  record Poly (I : Type₀) : Type₁ where
    field
      γₚ : I → Type₀
      ρₚ : {i : I} (c : γₚ i) → Type₀
      τₚ : {i : I} {c : γₚ i} (p : ρₚ c) → I

  open Poly
  
  ⟦_⟧ : {I : Type₀} (P : Poly I) → (I → Set) → I → Set
  ⟦ P ⟧ X i = Σ (γₚ P i) (λ c → (p : ρₚ P c) → X (τₚ P p))

  data W {I : Type₀} (P : Poly I) : I → Type₀ where
    lf : (i : I) → W P i
    nd : {i : I} → ⟦ P ⟧ (W P) i → W P i

  module _ {I : Type₀} (P : Poly I) where
  
    γ-fr : I → Type₀
    γ-fr = W P

    ρ-fr : {i : I} → γ-fr i → Type₀
    ρ-fr (lf i) = ⊤
    ρ-fr (nd (c , δ)) = Σ (ρₚ P c) (λ p → ρ-fr (δ p))

    τ-fr : {i : I} {c : γ-fr i} → ρ-fr c → I
    τ-fr {c = lf i} unit = i
    τ-fr {c = nd (c , δ)} (p₀ , p₁) = τ-fr p₁

    η-fr : (i : I) → γ-fr i
    η-fr = lf

    μ-fr : {i : I} (c : γ-fr i) (δ : (p : ρ-fr c) → γ-fr (τ-fr p)) → γ-fr i
    μ-fr (lf i) δ = δ unit
    μ-fr (nd (c , δ₀)) δ = nd (c , λ p₀ → μ-fr (δ₀ p₀) (λ p₁ → δ (p₀ , p₁)))

    ηρ-contr-fr : (i : I) → is-contr (ρ-fr (η-fr i))
    ηρ-contr-fr i = Unit-level

    μρ-to-fr : {i : I} {c : W P i}
               (δ : (p : ρ-fr c) → W P (τ-fr p)) →
               Σ (ρ-fr c) (λ x → ρ-fr (δ x)) → ρ-fr (μ-fr c δ)
    μρ-to-fr {c = lf i} δ (unit , p₁) = p₁
    μρ-to-fr {c = nd (c , δ₀)} δ ((p₀ , p₁) , p₂) = p₀ , μρ-to-fr (λ p₃ → δ (p₀ , p₃)) (p₁ , p₂)

    μρ-from-fr : {i : I} {c : W P i}
                 (δ : (p : ρ-fr c) → W P (τ-fr p)) →
                 ρ-fr (μ-fr c δ) → Σ (ρ-fr c) (λ x → ρ-fr (δ x))
    μρ-from-fr {c = lf i} δ p = unit , p
    μρ-from-fr {c = nd (c , δ₀)} δ (p₀ , p₁) =
      (p₀ , fst (μρ-from-fr (λ p₂ → δ (p₀ , p₂)) p₁)) , snd (μρ-from-fr (λ p₂ → δ (p₀ , p₂)) p₁)              

    μρ-to-from-fr : {i : I} {c : W P i}
                    (δ : (p : ρ-fr c) → W P (τ-fr p))
                    (p : ρ-fr (μ-fr c δ)) →
                    μρ-to-fr δ (μρ-from-fr δ p) == p
    μρ-to-from-fr {c = lf i} δ p = idp
    μρ-to-from-fr {c = nd (c , δ₀)} δ (p₀ , p₁) =
      ap (λ p₂ → (p₀ , p₂)) (μρ-to-from-fr (λ p₂ → δ (p₀ , p₂)) p₁)               

    μρ-from-to-fr : {i : I} {c : W P i}
                    (δ : (p : ρ-fr c) → W P (τ-fr p))
                    (p : Σ (ρ-fr c) (λ x → ρ-fr (δ x))) →
                    μρ-from-fr δ (μρ-to-fr δ p) == p
    μρ-from-to-fr {c = lf i} δ (unit , p₁) = idp
    μρ-from-to-fr {c = nd x} δ ((p₀ , p₁) , p₂) =
      pair= (pair= idp (fst= IH)) (↓-ap-in (ρ-fr ∘ δ) (λ x → (p₀ , x)) (snd= IH))
    
      where IH : μρ-from-fr (λ p₃ → δ (p₀ , p₃)) (μρ-to-fr (λ p₃ → δ (p₀ , p₃)) (p₁ , p₂)) == p₁ , p₂
            IH = μρ-from-to-fr (λ p₃ → δ (p₀ , p₃)) (p₁ , p₂)

    μρ-equiv-fr : {i : I} {c : γ-fr i}
                  (δ : (p : ρ-fr c) → γ-fr (τ-fr p)) → 
                  Σ (ρ-fr c) (ρ-fr ∘ δ) ≃ ρ-fr (μ-fr c δ)
    μρ-equiv-fr δ = equiv (μρ-to-fr δ) (μρ-from-fr δ) (μρ-to-from-fr δ) (μρ-from-to-fr δ)




