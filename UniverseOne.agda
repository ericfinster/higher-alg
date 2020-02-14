{-# OPTIONS --without-K --rewriting --type-in-type #-}

open import Base

module UniverseOne where

  --
  --  Dimension 1 - Contexts
  --
  
  data Ctx : Set where
    nil : Ctx
    cns : (A : Set) (B : A → Ctx) → Ctx

  CtxPos : Ctx → Set
  CtxPos nil = ⊥
  CtxPos (cns A B) = ⊤ ⊔ Σ A (λ a → CtxPos (B a))

  CtxTyp : (Γ : Ctx) (p : CtxPos Γ) → Set
  CtxTyp nil ()
  CtxTyp (cns A B) (inl unit) = A
  CtxTyp (cns A B) (inr (a , p)) = CtxTyp (B a) p
  
  data Σ↓ : Ctx → Set where
    nil↓ : Σ↓ nil
    cns↓ : {A : Set} {B : A → Ctx}
      → (a : A) (b : Σ↓ (B a))
      → Σ↓ (cns A B)

  η₁ : Set → Ctx
  η₁ A = cns A (λ _ → nil)

  γ₁ : (Γ : Ctx) (δ : Σ↓ Γ  → Ctx) → Ctx
  γ₁ nil δ = δ nil↓
  γ₁ (cns A B) δ = cns A (λ a → γ₁ (B a) (λ b↓ → δ (cns↓ a b↓)))
  
  γ₁-fst : (Γ : Ctx)
    → (δ : Σ↓ Γ  → Ctx) 
    → (s : Σ↓ (γ₁ Γ δ))
    → Σ↓ Γ
  γ₁-fst nil δ s = nil↓
  γ₁-fst (cns A B) δ (cns↓ a s) =
    cns↓ a (γ₁-fst (B a) (λ b↓ → δ (cns↓ a b↓)) s)
  
  γ₁-snd : (Γ : Ctx)
    → (δ : Σ↓ Γ  → Ctx) 
    → (s : Σ↓ (γ₁ Γ δ))
    → Σ↓ (δ (γ₁-fst Γ δ s))
  γ₁-snd nil δ s = s
  γ₁-snd (cns A B) δ (cns↓ a s) =
    γ₁-snd (B a) (λ b↓ → δ (cns↓ a b↓)) s

  postulate

    γ₁-unit-r : (Γ : Ctx)
      → γ₁ Γ (λ _ → nil) ↦ Γ
    {-# REWRITE γ₁-unit-r #-}

  --
  --  Equivalences
  --

  record Eqv (A B : Set) : Set where
    field
      Wit : A → B → Set
      To : A → B
      ToWit : (a : A) → Wit a (To a)
      From : B → A
      FromWit : (b : B) → Wit (From b) b

  open Eqv public
