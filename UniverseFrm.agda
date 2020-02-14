{-# OPTIONS --without-K --rewriting --type-in-type --no-positivity #-}

open import Base

module UniverseFrm where

  --
  --  Basic Signature
  --

  data Frm : ℕ → Set
  Cell : {n : ℕ} → Frm n → Set
  
  data Tree : {n : ℕ} → Frm n → Set
  Pos : {n : ℕ} {f : Frm n} (σ : Tree f) → Set

  Typ : {n : ℕ} {f : Frm n} (σ : Tree f) (p : Pos σ) → Frm n
  Inh : {n : ℕ} {f : Frm n} (σ : Tree f) (p : Pos σ) → Cell (Typ σ p)

  infixl 30 _∣_▸_ 

  data Frm where
    ● : Frm O
    _∣_▸_ : {n : ℕ} (f : Frm n)
      → Tree {n} f → Cell {n} f
      → Frm (S n)

  -- Okay, so it seems one of the central difficulties is that you
  -- force the indices of trees and cells to be the same up to
  -- definitional equality.  But I now think this is somehow a bit
  -- unrealistic.  This is because it seems that for the universe,
  -- μ does not preserve the fram definitionally.  How can we weaken
  -- this assumption somehow to take this into account?
  
  Cell = {!!}

  η : {n : ℕ} (f : Frm n)
    → Cell {n} f
    → Tree {n} f
  η = {!!}

  μ-frm : {n : ℕ} (f : Frm n) (σ : Tree {n} f) 
    → (δ : (p : Pos σ) → Tree {n} (Typ σ p))
    → (ε : (p : Pos σ) → Tree {S n} (Typ σ p ∣ δ p ▸ Inh σ p))
    → Frm n 

  μ : {n : ℕ} (f : Frm n) (σ : Tree {n} f) 
    → (δ : (p : Pos σ) → Tree {n} (Typ σ p))
    → (ε : (p : Pos σ) → Tree {S n} (Typ σ p ∣ δ p ▸ Inh σ p))
    → Tree (μ-frm f σ δ ε)

  μ = {!!}
  μ-frm = {!!}
  
  data Tree where

    lf : {n : ℕ} (f : Frm n) (τ : Cell {n} f)
      → Tree {S n} (f ∣ η f τ ▸ τ) 
    nd : {n : ℕ} (f : Frm n)
      → (σ : Tree {n} f) (τ : Cell {n} f)
      → (θ : Cell {S n} (f ∣ σ ▸ τ))
      → (δ : (p : Pos σ) → Tree {n} (Typ σ p))
      → (ε : (p : Pos σ) → Tree {S n} (Typ σ p ∣ δ p ▸ Inh σ p))
      → Tree {S n} (f ∣ μ f σ δ ε ▸ τ)

  Pos = {!!}
  Typ = {!!}
  Inh = {!!}
