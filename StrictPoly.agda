{-# OPTIONS --without-K --rewriting --strict-poly-monads #-}

open import Agda.Primitive using (lzero)
  renaming (Level to ULevel; lsuc to lsucc; _⊔_ to lmax)

module StrictPoly where

  record ⊤ : Set₀ where
    constructor unit

  {-# BUILTIN UNIT ⊤ #-}

  data _⊔_ {ℓ κ} (A : Set ℓ) (B : Set κ) : Set (lmax ℓ κ) where
    inl : A → A ⊔ B
    inr : B → A ⊔ B

  {-# BUILTIN COPROD _⊔_ #-}
  {-# BUILTIN INL inl #-}
  {-# BUILTIN INR inr #-}

  data ⊥ {ℓ} : Set ℓ where

  {-# BUILTIN EMPTY ⊥ #-}

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
