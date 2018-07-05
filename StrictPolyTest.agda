{-# OPTIONS --without-K --rewriting --strict-poly-monads --verbose=tc.meta.eta:30 --verbose=tc.conv.term:30 --verbose=tc.lhs:80 --verbose=tc.meta.assign.proj:40 #-}

open import HoTT
open import StrictPoly

module StrictPolyTest where
    
  module _ {ℓ} (M : Mnd ℓ) where

    -- Place reduction tests
    
    -- ηρ-τ : (i : Idx M) (p : ρ M i (η M i))
    --   → τ M i (η M i) p == i
    -- ηρ-τ i p = idp

    -- μρ-τ : (i : Idx M) (c : γ M i)
    --   → (δ : (p : ρ M i c) → γ M (τ M i c p))
    --   → (p : ρ M i (μ M i c δ))
    --   → τ M i (μ M i c δ) p == τ M (τ M i c (μρ-fst M i c δ p)) (δ (μρ-fst M i c δ p)) (μρ-snd M i c δ p)
    -- μρ-τ i c δ p = idp

    -- μρ-fst-β : (i : Idx M) (c : γ M i)
    --   → (δ : (p : ρ M i c) → γ M (τ M i c p)) 
    --   → (p₀ : ρ M i c) (p₁ : ρ M (τ M i c p₀) (δ p₀))
    --   → μρ-fst M i c δ (μρ M i c δ p₀ p₁) == p₀
    -- μρ-fst-β i c δ p₀ p₁ = idp

    -- μρ-snd-β : (i : Idx M) (c : γ M i)
    --   → (δ : (p : ρ M i c) → γ M (τ M i c p)) 
    --   → (p₀ : ρ M i c) (p₁ : ρ M (τ M i c p₀) (δ p₀))
    --   → μρ-snd M i c δ (μρ M i c δ p₀ p₁) == p₁
    -- μρ-snd-β i c δ p₀ p₁ = idp

    -- Monad laws

    -- unit-l : (i : Idx M) (c : γ M i) 
    --   → μ M i c (λ p → η M (τ M i c p)) == c
    -- unit-l i c = idp

    -- unit-r : (i : Idx M)
    --   → (δ : (p : ρ M i (η M i)) → γ M (τ M i (η M i) p)) 
    --   → μ M i (η M i) δ == δ (ηρ M i)
    -- unit-r i δ = idp

    -- assoc : (i : Idx M) (c : γ M i)
    --   → (δ : (p : ρ M i c) → γ M (τ M i c p))
    --   → (ε : (q : ρ M i (μ M i c δ)) → γ M (τ M i (μ M i c δ) q)) 
    --   → μ M i (μ M i c δ) ε == μ M i c (λ p → μ M (τ M i c p) (δ p) (λ q → ε (μρ M i c δ p q)))
    -- assoc i c δ ε = idp

    -- Eta tests
    ηρ-η : (i : Idx M) (p : ρ M i (η M i))
      → ηρ M i == p
    ηρ-η i p = {!idp!}

    -- μρ-η : (i : Idx M) (c : γ M i)
    --   → (δ : (p : ρ M i c) → γ M (τ M i c p)) 
    --   → (p : ρ M i (μ M i c δ))
    --   → μρ M i c δ (μρ-fst M i c δ p) (μρ-snd M i c δ p) == p
    -- μρ-η i c δ p = {!!}
