{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module Universe where

  -- So, here are telescopes
  data Tele : Type₀ → Type₁ where
    ε : Tele ⊤
    σ : (X : Type₀) (P₀ : X → Type₀)
        → (P₁ : (x : X) → Tele (P₀ x))
        → Tele (Σ X P₀)

  -- Their places, which are partial substitutions.
  TelePlc : (X : Set₀) (T : Tele X) → Set₀
  TelePlc .⊤ ε = ⊥
  TelePlc .(Σ X P₀) (σ X P₀ P₁) = ⊤ ⊔ (Σ X (λ x → TelePlc (P₀ x) (P₁ x)))

  -- And their types, which pull back the sequence along a
  -- partial substitution.
  TeleTyp : (X : Set₀) (T : Tele X) (t : TelePlc X T) → Set₀
  TeleTyp .⊤ ε ()
  TeleTyp .(Σ X P₀) (σ X P₀ P₁) true = X
  TeleTyp .(Σ X P₀) (σ X P₀ P₁) (inr (x , T)) = TeleTyp (P₀ x) (P₁ x) T
