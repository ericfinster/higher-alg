{-# OPTIONS --without-K --rewriting #-}

module Base where

  -- Rewriting
  infix 30 _↦_
  postulate  
    _↦_ : ∀ {i} {A : Set i} → A → A → Set i

  {-# BUILTIN REWRITE _↦_ #-}

  infixr 60 _,_ _×_

  record Σ (A : Set) (B : A → Set) : Set where
    constructor _,_
    field
      fst : A
      snd : B fst

  open Σ public

  _×_ : Set → Set → Set
  A × B = Σ A (λ _ → B)

  record ⊤ : Set where
    instance constructor unit

  Unit = ⊤

  {-# BUILTIN UNIT ⊤ #-}

  data ℕ : Set where
    O : ℕ
    S : ℕ → ℕ

  {-# BUILTIN NATURAL ℕ #-}

