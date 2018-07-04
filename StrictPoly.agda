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

primitive

  primPolyIdx : ∀ {ℓ} → Mnd ℓ → Set ℓ
  primPolyCons : ∀ {ℓ} (M : Mnd ℓ) → primPolyIdx M → Set ℓ
  primPolyPlc : ∀ {ℓ} (M : Mnd ℓ) (i : primPolyIdx M) → primPolyCons M i → Set ℓ
  primPolyTyp : ∀ {ℓ} (M : Mnd ℓ) (i : primPolyIdx M) (c : primPolyCons M i)
    → primPolyPlc M i c → primPolyIdx M

Idx = primPolyIdx
γ = primPolyCons
ρ = primPolyPlc
τ = primPolyTyp

postulate

  pb : ∀ {ℓ} (M : Mnd ℓ) (X : Idx M → Set ℓ) → Mnd ℓ

{-# BUILTIN PBMND pb #-}

primitive

  primPolyUnit : ∀ {ℓ} (M : Mnd ℓ) (i : Idx M) → γ M i
  primPolyMult : ∀ {ℓ} (M : Mnd ℓ)
    → (i : Idx M) (c : γ M i)
    → (δ : (p : ρ M i c) → γ M (τ M i c p))
    → γ M i

η = primPolyUnit
μ = primPolyMult

primitive

  primPolyUnitPlc : ∀ {ℓ} (M : Mnd ℓ) (i : Idx M) → ρ M i (η M i)

  primPolyMultPlc : ∀ {ℓ} (M : Mnd ℓ)
    → (i : Idx M) (c : γ M i)
    → (δ : (p : ρ M i c) → γ M (τ M i c p))
    → (p₀ : ρ M i c) (p₁ : ρ M (τ M i c p₀) (δ p₀))
    → ρ M i (μ M i c δ)

  primPolyMultFst : ∀ {ℓ} (M : Mnd ℓ)
    → (i : Idx M) (c : γ M i)
    → (δ : (p : ρ M i c) → γ M (τ M i c p))
    → (p : ρ M i (μ M i c δ))
    → ρ M i c

  primPolyMultSnd : ∀ {ℓ} (M : Mnd ℓ)
    → (i : Idx M) (c : γ M i)
    → (δ : (p : ρ M i c) → γ M (τ M i c p))
    → (p : ρ M i (μ M i c δ))
    → ρ M (τ M i c (primPolyMultFst M i c δ p)) (δ (primPolyMultFst M i c δ p))

ηρ = primPolyUnitPlc
μρ = primPolyMultPlc
μρ-fst = primPolyMultFst
μρ-snd = primPolyMultSnd

data Nst {ℓ} (M : Mnd ℓ) : (i : Idx M) → (c : γ M i) → Set ℓ where
  dot : (i : Idx M) → Nst M i (η M i)
  box : (i : Idx M) (c : γ M i)
        (δ : (p : ρ M i c) → γ M (τ M i c p))
        (ε : (p : ρ M i c) → Nst M (τ M i c p) (δ p)) →
        Nst M i (μ M i c δ)

{-# BUILTIN SLCCONS Nst #-}
{-# BUILTIN SLCCONSDOT dot #-}
{-# BUILTIN SLCCONSBOX box #-}

primitive

  primPolyGraft : ∀ {ℓ} (M : Mnd ℓ)
    → (i : Idx M) (c : γ M i) (n : Nst M i c)
    → (δ₁ : (p : ρ M i c) → γ M (τ M i c p))
    → (ε₁ : (p : ρ M i c) → Nst M (τ M i c p) (δ₁ p)) 
    → Nst M i (μ M i c δ₁)

  primPolyGraftPlcTo : ∀ {ℓ} (M : Mnd ℓ)
    → (i : Idx M) (c : γ M i) (n : Nst M i c)
    → (δ₁ : (p : ρ M i c) → γ M (τ M i c p))
    → (ε₁ : (p : ρ M i c) → Nst M (τ M i c p) (δ₁ p)) 
    → ρ (slc M) (i , c) n ⊔ Σ (ρ M i c) (λ p → ρ (slc M) (τ M i c p , δ₁ p) (ε₁ p))
    → ρ (slc M) (i , μ M i c δ₁) (primPolyGraft M i c n δ₁ ε₁)

  primPolyGraftPlcFrom : ∀ {ℓ} (M : Mnd ℓ)
    → (i : Idx M) (c : γ M i) (n : Nst M i c)
    → (δ₁ : (p : ρ M i c) → γ M (τ M i c p))
    → (ε₁ : (p : ρ M i c) → Nst M (τ M i c p) (δ₁ p)) 
    → ρ (slc M) (i , μ M i c δ₁) (primPolyGraft M i c n δ₁ ε₁)
    → ρ (slc M) (i , c) n ⊔ Σ (ρ M i c) (λ p → ρ (slc M) (τ M i c p , δ₁ p) (ε₁ p))

