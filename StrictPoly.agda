{-# OPTIONS --without-K --rewriting --strict-poly-monads #-}

open import HoTT

module StrictPoly where

  data ⊥₀ {ℓ} : Set ℓ where

  {-# BUILTIN EMPTY ⊥₀ #-}

  postulate

    Mnd : (ℓ : ULevel) → Set (lsucc ℓ)
    id : ∀ {ℓ} → Set ℓ → Mnd ℓ 
    slc : ∀ {ℓ} → Mnd ℓ → Mnd ℓ

  {-# BUILTIN POLYMND Mnd #-}
  {-# BUILTIN IDMND id #-}
  {-# BUILTIN SLCMND slc #-}

  postulate

    Idx : ∀ {ℓ} → Mnd ℓ → Set ℓ
    γ : ∀ {ℓ} (M : Mnd ℓ) → Idx M → Set ℓ
    ρ : ∀ {ℓ} (M : Mnd ℓ) (i : Idx M) → γ M i → Set ℓ
    τ : ∀ {ℓ} (M : Mnd ℓ) (i : Idx M) (c : γ M i)
      → ρ M i c → Idx M

  {-# BUILTIN POLYIDX Idx #-}
  {-# BUILTIN POLYCONS γ #-}
  {-# BUILTIN POLYPLC ρ #-}
  {-# BUILTIN POLYTYP τ #-}

  ⟪_⟫ : ∀ {ℓ} (M : Mnd ℓ) (X : Idx M → Set ℓ) → Idx M → Set ℓ
  ⟪ M ⟫ X i = Σ (γ M i) (λ c → (p : ρ M i c) → X (τ M i c p))

  postulate

    pb : ∀ {ℓ} (M : Mnd ℓ) (X : Idx M → Set ℓ) → Mnd ℓ

  {-# BUILTIN PBMND pb #-}

  postulate

    η : ∀ {ℓ} (M : Mnd ℓ) (i : Idx M) → γ M i
    ηρ : ∀ {ℓ} (M : Mnd ℓ) (i : Idx M) → ρ M i (η M i)

    μ : ∀ {ℓ} (M : Mnd ℓ)
      → (i : Idx M) (c : γ M i)
      → (δ : (p : ρ M i c) → γ M (τ M i c p))
      → γ M i

    μρ : ∀ {ℓ} (M : Mnd ℓ)
      → (i : Idx M) (c : γ M i)
      → (δ : (p : ρ M i c) → γ M (τ M i c p))
      → (p₀ : ρ M i c) (p₁ : ρ M (τ M i c p₀) (δ p₀))
      → ρ M i (μ M i c δ)

    μρ-fst : ∀ {ℓ} (M : Mnd ℓ)
      → (i : Idx M) (c : γ M i)
      → (δ : (p : ρ M i c) → γ M (τ M i c p))
      → (p : ρ M i (μ M i c δ))
      → ρ M i c

    μρ-snd : ∀ {ℓ} (M : Mnd ℓ)
      → (i : Idx M) (c : γ M i)
      → (δ : (p : ρ M i c) → γ M (τ M i c p))
      → (p : ρ M i (μ M i c δ))
      → ρ M (τ M i c (μρ-fst M i c δ p)) (δ (μρ-fst M i c δ p))

  {-# BUILTIN POLYUNIT η #-}
  {-# BUILTIN POLYUNITPLC ηρ #-}
  {-# BUILTIN POLYMULT μ #-}
  {-# BUILTIN POLYMULTPLC μρ #-}
  {-# BUILTIN POLYMULTFST μρ-fst #-}
  {-# BUILTIN POLYMULTSND μρ-snd #-}

  data Nst {ℓ} (M : Mnd ℓ) : (i : Idx M) → (c : γ M i) → Set ℓ where
    dot : (i : Idx M) → Nst M i (η M i)
    box : (i : Idx M) (c : γ M i)
          (δ : (p : ρ M i c) → γ M (τ M i c p))
          (ε : (p : ρ M i c) → Nst M (τ M i c p) (δ p)) →
          Nst M i (μ M i c δ)

  {-# BUILTIN SLCCONS Nst #-}
  {-# BUILTIN SLCCONSDOT dot #-}
  {-# BUILTIN SLCCONSBOX box #-}

  postulate

    graft-slc : ∀ {ℓ} (M : Mnd ℓ)
      → (i : Idx M) (c : γ M i) (n : Nst M i c)
      → (δ₁ : (p : ρ M i c) → γ M (τ M i c p))
      → (ε₁ : (p : ρ M i c) → Nst M (τ M i c p) (δ₁ p)) 
      → Nst M i (μ M i c δ₁)

    graft-slc-ρ-to : ∀ {ℓ} (M : Mnd ℓ)
      → (i : Idx M) (c : γ M i) (n : Nst M i c)
      → (δ₁ : (p : ρ M i c) → γ M (τ M i c p))
      → (ε₁ : (p : ρ M i c) → Nst M (τ M i c p) (δ₁ p)) 
      → ρ (slc M) (i , c) n ⊔ Σ (ρ M i c) (λ p → ρ (slc M) (τ M i c p , δ₁ p) (ε₁ p))
      → ρ (slc M) (i , μ M i c δ₁) (graft-slc M i c n δ₁ ε₁)

    graft-slc-ρ-from : ∀ {ℓ} (M : Mnd ℓ)
      → (i : Idx M) (c : γ M i) (n : Nst M i c)
      → (δ₁ : (p : ρ M i c) → γ M (τ M i c p))
      → (ε₁ : (p : ρ M i c) → Nst M (τ M i c p) (δ₁ p)) 
      → ρ (slc M) (i , μ M i c δ₁) (graft-slc M i c n δ₁ ε₁)
      → ρ (slc M) (i , c) n ⊔ Σ (ρ M i c) (λ p → ρ (slc M) (τ M i c p , δ₁ p) (ε₁ p))

  {-# BUILTIN POLYGRAFT graft-slc #-}
  {-# BUILTIN POLYGRAFTPLCTO graft-slc-ρ-to #-}
  {-# BUILTIN POLYGRAFTPLCFROM graft-slc-ρ-from #-}
