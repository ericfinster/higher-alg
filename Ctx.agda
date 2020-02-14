{-# OPTIONS --without-K --rewriting --type-in-type #-}

open import Base

module Ctx where

  --
  --  Contexts
  --
  
  data Ctx : Set where
    nil : Ctx
    cns : (A : Set) (B : A → Ctx) → Ctx

  data CtxPos : Ctx → Set where
    cns-here : (A : Set) (B : A → Ctx) → CtxPos (cns A B)
    cns-there : (A : Set) (B : A → Ctx)
      → (a : A) (p : CtxPos (B a))
      → CtxPos (cns A B)

  CtxTyp : (Γ : Ctx) (p : CtxPos Γ) → Set
  CtxTyp .(cns A B) (cns-here A B) = A
  CtxTyp .(cns A B) (cns-there A B a p) = CtxTyp (B a) p
  
  data Σ↓ : Ctx → Set where
    nil↓ : Σ↓ nil
    cns↓ : {A : Set} {B : A → Ctx}
      → (a : A) (b : Σ↓ (B a))
      → Σ↓ (cns A B)

  γ-ctx : (Γ : Ctx) (δ : Σ↓ Γ  → Ctx) → Ctx
  γ-ctx nil δ = δ nil↓
  γ-ctx (cns A B) δ = cns A (λ a → γ-ctx (B a) (λ b↓ → δ (cns↓ a b↓)))
  
  γ-ctx-fst : (Γ : Ctx)
    → (δ : Σ↓ Γ  → Ctx) 
    → (s : Σ↓ (γ-ctx Γ δ))
    → Σ↓ Γ
  γ-ctx-fst nil δ s = nil↓
  γ-ctx-fst (cns A B) δ (cns↓ a s) =
    cns↓ a (γ-ctx-fst (B a) (λ b↓ → δ (cns↓ a b↓)) s)
  
  γ-ctx-snd : (Γ : Ctx)
    → (δ : Σ↓ Γ  → Ctx) 
    → (s : Σ↓ (γ-ctx Γ δ))
    → Σ↓ (δ (γ-ctx-fst Γ δ s))
  γ-ctx-snd nil δ s = s
  γ-ctx-snd (cns A B) δ (cns↓ a s) =
    γ-ctx-snd (B a) (λ b↓ → δ (cns↓ a b↓)) s

  --
  --  Equivalences
  --

  record Eqv (A B : Set) : Set where
    field
      Wit : A → B → Set
      To : A → B
      ToWit : (a : A) → Wit a (To a)
      From : B → A
      FromWith : (b : B) → Wit (From b) b
      -- ... and the coherences ....
      
  open Eqv
