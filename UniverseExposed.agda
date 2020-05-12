{-# OPTIONS --without-K --rewriting --type-in-type #-}

open import Base
open import Ctx

module UniverseExposed where

  data Frm : (A : Set) (β : Tree₂ A) (E : Eqv (Σ↓ (∂₂ β)) A) → ℕ → Set 
  data Tree : (A : Set)
    → (β : Tree₂ A) (E : Eqv (Σ↓ (∂₂ β)) A)
    → (n : ℕ) (f : Frm A β E n) → Set

  Cell : (A : Set)
    → (β : Tree₂ A) (E : Eqv (Σ↓ (∂₂ β)) A)
    → (n : ℕ) (f : Frm A β E n)
    → Set

  Pos : {A : Set}
    → {β : Tree₂ A} {E : Eqv (Σ↓ (∂₂ β)) A}
    → {n : ℕ} {f : Frm A β E n}
    → Tree A β E n f → Set

  Typ : {A : Set}
    → {β : Tree₂ A} {E : Eqv (Σ↓ (∂₂ β)) A}
    → {n : ℕ} {f : Frm A β E n}
    → (σ : Tree A β E n f) (p : Pos σ)
    → Frm A β E n 

  Inh : {A : Set}
    → {β : Tree₂ A} {E : Eqv (Σ↓ (∂₂ β)) A}
    → {n : ℕ} {f : Frm A β E n}
    → (σ : Tree A β E n f) (p : Pos σ)
    → Cell A β E n (Typ σ p)

    
  data Frm where
    ● : {A : Set} {β : Tree₂ A} {E : Eqv (Σ↓ (∂₂ β)) A}
      → Frm A β E O
    _∣_▸_ : {A : Set}
      → {β : Tree₂ A} {E : Eqv (Σ↓ (∂₂ β)) A}
      → {n : ℕ} (f : Frm A β E n)
      → (σ : Tree A β E n f) (τ : Cell A β E n f)
      → Frm A β E (S n)

  η : {A : Set}
    → {β : Tree₂ A} {E : Eqv (Σ↓ (∂₂ β)) A}
    → {n : ℕ} (f : Frm A β E n)
    → Cell A β E n f → Tree A β E n f

  μ : {A : Set}
    → {β : Tree₂ A} {E : Eqv (Σ↓ (∂₂ β)) A}
    → {n : ℕ} (f : Frm A β E n)
    → (σ : Tree A β E n f)
    → (δ : (p : Pos σ) → Tree A β E n (Typ σ p))
    → Tree A β E n f

  γ : {A : Set}
    → {β : Tree₂ A} {E : Eqv (Σ↓ (∂₂ β)) A}
    → {n : ℕ} (f : Frm A β E n)
    → (σ : Tree A β E n f)
    → (δ : (p : Pos σ) → Tree A β E n (Typ σ p))
    → (ε : (p : Pos σ) → Tree A β E (S n) (Typ σ p ∣ δ p ▸ Inh σ p))
    → Tree A β E n f

  data Tree where

    lf₃ : (Γ : Ctx) (A : Set) (E : Eqv (Σ↓ Γ) A)
      → Tree A (nd₂ Γ A E (λ p → lf₂ (CtxTyp Γ p))) E O ● 

    nd₃ : (A : Set) (β : Tree₂ A) 
      → (δ : (p : Pos₂ β) → Σ (Tree₂ (TgtSet β p)) (λ τ → ∂₂ τ == SrcCtx β p))
      -- And here we need a transport ... (which technically is not a
      -- problem but looks a bit ugly ...)
      → (ε : (p : Pos₂ β) → Tree (TgtSet β p) (fst (δ p)) {!Inh₂ β p!} O ●)
      → (E : Eqv (Σ↓ (∂₂ (μ₂ β δ))) A)
      -- Right, so what will be the type of this guy?
      → {!!}
      → Tree A (μ₂ β δ) E O ●

    lf : {A : Set}
      → {β : Tree₂ A} {E : Eqv (Σ↓ (∂₂ β)) A}
      → {n : ℕ} (f : Frm A β E n)
      → (C : Cell A β E n f)
      → Tree A β E (S n) (f ∣ η f C ▸ C)
    nd : {A : Set}
      → {β : Tree₂ A} {E : Eqv (Σ↓ (∂₂ β)) A}
      → {n : ℕ} (f : Frm A β E n)
      → (σ : Tree A β E n f) (τ : Cell A β E n f)
      → (δ : (p : Pos σ) → Tree A β E n (Typ σ p))
      → (ε : (p : Pos σ) → Tree A β E (S n) (Typ σ p ∣ δ p ▸ Inh σ p))
      → (θ : Cell A β E (S n) (f ∣ σ ▸ τ))
      → Tree A β E (S n) (f ∣ μ f σ δ ▸ τ)


  η = {!!}
  
  -- μ : {A : Set}
  --   → {β : Tree₂ A} {E : Eqv (Σ↓ (∂₂ β)) A}
  --   → {n : ℕ} (f : Frm A β E n)
  --   → (σ : Tree A β E n f)
  --   → (δ : (p : Pos σ) → Tree A β E n (Typ σ p))
  --   → Tree A β E n f
  μ {n = O} ● (lf₃ Γ A E) δ₁ = lf₃ Γ A E
  μ {n = O} ● (nd₃ A β δ ε E _) δ₁ = {!γ!}

  -- Okay.  But now it looks like γ will indeed give you
  -- the type that you want.  The trouble is going to be
  -- constructing the decoration.  But I don't see that this
  -- is a problem in principle, only that it will be a bit
  -- messy.
  
  μ {n = S n} f σ δ = {!!}

  γ = {!!}

  Cell = {!!}
  Pos = {!!}
  Typ = {!!}
  Inh = {!!}
