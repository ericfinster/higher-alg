{-# OPTIONS --without-K --rewriting --type-in-type #-}

open import Base
open import Ctx

module UniverseExposed where

  data Frm : Ctx → Set → ℕ → Set
  Cell : (Γ : Ctx) (A : Set) (n : ℕ) → Frm Γ A n → Set
  
  data Tree : (Γ : Ctx) (A : Set) (n : ℕ) → Frm Γ A n → Set
  Pos : (Γ : Ctx) (A : Set) (n : ℕ)
    → (f : Frm Γ A n) → Tree Γ A n f → Set


  data Frm where
    _▸_ : (Γ : Ctx) (A : Set) → Frm Γ A O
    -- Well, with this definition, we simply follow the previous
    -- setup.  But with the context exposed, here we could allow
    -- the cell to live in a context computed from the tree, right?
    -- Hmmm.  No, because the the frame is not right....
    _∣_▸_ : {Γ : Ctx} {A : Set} {n : ℕ}
      → (f : Frm Γ A n) (σ : Tree Γ A n f) (τ : Cell Γ A n f)
      → Frm Γ A (S n)

  Cell = {!!}

  η : {Γ : Ctx} {A : Set} {n : ℕ} (f : Frm Γ A n)
    → Cell Γ A n f → Tree Γ A n f
  η = {!!}
  
  data Tree where
    lf : (Γ : Ctx) (A : Set) (n : ℕ) (f : Frm Γ A n)
      → (E : Cell Γ A n f)
      → Tree Γ A (S n) (f ∣ η f E ▸ E)
    nd : (Γ : Ctx) (A : Set) (n : ℕ) (f : Frm Γ A n)
      → Tree {!!} A n {!!} 

    -- nd : {n : ℕ} (f : Frm (S n))
    --    → (σ : Tree {S n} f) (τ : Cell {S n} f)
    --    → (C : Cell {S (S n)} (f , σ , τ))
    --    → (δ : (p : Pos σ) → Tree {S n} (Typ σ p))
    --    → (ε : (p : Pos σ) → Tree {S (S n)} (Typ σ p , δ p , Inh σ p))
    --    → Tree {S (S n)} (f , μ f σ δ , τ)


  Pos = {!!}


  -- μ : {n : ℕ} (f : Frm (S n)) (σ : Tree {S n} f) 
  --   → (δ : (p : Pos σ) → Tree {S n} (Typ σ p))
  --   → Tree {S n} f
