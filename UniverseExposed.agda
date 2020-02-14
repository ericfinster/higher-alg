{-# OPTIONS --without-K --rewriting --type-in-type #-}

open import Base
open import Ctx

module UniverseExposed where


  data Tree₂ : Ctx → Set → Set 

  data Tree₂ where

  postulate

    Pos₂ : {Γ : Ctx} {A : Set} → Tree₂ Γ A → Set
    
    SrcCtx : {Γ : Ctx} {A : Set} (σ : Tree₂ Γ A) → Pos₂ σ → Ctx
    TgtSet : {Γ : Ctx} {A : Set} (σ : Tree₂ Γ A) → Pos₂ σ → Set

    Inh₂ : {Γ : Ctx} {A : Set} (σ : Tree₂ Γ A) (p : Pos₂ σ)
      → Eqv (Σ↓ (SrcCtx σ p)) (TgtSet σ p)

    μ₁ : (Γ : Ctx)
      → (δ : (p : CtxPos Γ) → Ctx)
      → (ε : (p : CtxPos Γ) → Tree₂ (δ p) (CtxTyp Γ p))
      → Ctx
      
    γ₂ : (Γ : Ctx) (A : Set) (σ : Tree₂ Γ A)
      → (δ : (p : CtxPos Γ) → Ctx)
      → (ε : (p : CtxPos Γ) → Tree₂ (δ p) (CtxTyp Γ p))
      → Tree₂ (μ₁ Γ δ ε) A

    η₂ : (Γ : Ctx) (A : Set)
      → Eqv (Σ↓ Γ) A
      → Tree₂ Γ A
      
    -- Right.  And this is where you hope to be able
    -- to "discard" some information ....
    μ₂ : {Γ : Ctx} {A : Set}
      → (β : Tree₂ Γ A) 
      → (δ : (p : Pos₂ β) → Tree₂ (SrcCtx β p) (TgtSet β p))
      → Tree₂ Γ A

  data Frm : (Γ : Ctx) (A : Set) (β : Tree₂ Γ A) (E : Eqv (Σ↓ Γ) A) → ℕ → Set 
  data Tree : (Γ : Ctx) (A : Set)
    → (β : Tree₂ Γ A) (E : Eqv (Σ↓ Γ) A)
    → (n : ℕ) (f : Frm Γ A β E n) → Set

  Cell : (Γ : Ctx) (A : Set)
    → (β : Tree₂ Γ A) (E : Eqv (Σ↓ Γ) A)
    → (n : ℕ) (f : Frm Γ A β E n)
    → Set

  Pos : {Γ : Ctx} {A : Set}
    → {β : Tree₂ Γ A} {E : Eqv (Σ↓ Γ) A}
    → {n : ℕ} {f : Frm Γ A β E n}
    → Tree Γ A β E n f → Set

  Typ : {Γ : Ctx} {A : Set}
    → {β : Tree₂ Γ A} {E : Eqv (Σ↓ Γ) A}
    → {n : ℕ} {f : Frm Γ A β E n}
    → (σ : Tree Γ A β E n f) (p : Pos σ)
    → Frm Γ A β E n 

  Inh : {Γ : Ctx} {A : Set}
    → {β : Tree₂ Γ A} {E : Eqv (Σ↓ Γ) A}
    → {n : ℕ} {f : Frm Γ A β E n}
    → (σ : Tree Γ A β E n f) (p : Pos σ)
    → Cell Γ A β E n (Typ σ p)

    
  data Frm where
    ● : {Γ : Ctx} {A : Set} {β : Tree₂ Γ A} {E : Eqv (Σ↓ Γ) A}
      → Frm Γ A β E O
    _∣_▸_ : {Γ : Ctx} {A : Set}
      → {β : Tree₂ Γ A} {E : Eqv (Σ↓ Γ) A}
      → {n : ℕ} (f : Frm Γ A β E n)
      → (σ : Tree Γ A β E n f) (τ : Cell Γ A β E n f)
      → Frm Γ A β E (S n)

  η : {Γ : Ctx} {A : Set}
    → {β : Tree₂ Γ A} {E : Eqv (Σ↓ Γ) A}
    → {n : ℕ} (f : Frm Γ A β E n)
    → Cell Γ A β E n f → Tree Γ A β E n f

  μ : {Γ : Ctx} {A : Set}
    → {β : Tree₂ Γ A} {E : Eqv (Σ↓ Γ) A}
    → {n : ℕ} (f : Frm Γ A β E n)
    → (σ : Tree Γ A β E n f)
    → (δ : (p : Pos σ) → Tree Γ A β E n (Typ σ p))
    → Tree Γ A β E n f

  data Tree where

    -- lf₀ : (A : Set) (β : Tree₂ A) (E : Eqv (Σ↓ (μ₂ A β)) A)
    --   → Tree A β E O (● A β E)
    lf₀ : (Γ : Ctx) (A : Set)
      → (E : Eqv (Σ↓ Γ) A)
      → Tree Γ A (η₂ Γ A E) E O ●

    nd₀ : (Γ : Ctx) (A : Set)
      → (β : Tree₂ Γ A) (E : Eqv (Σ↓ Γ) A)
      -- Oh! And the extra equivalence here ...
      → (δ : (p : Pos₂ β) → Tree₂ (SrcCtx β p) (TgtSet β p))
      → (ε : (p : Pos₂ β) → Tree (SrcCtx β p) (TgtSet β p) (δ p) (Inh₂ β p) O ●)
      → Tree Γ A (μ₂ β δ) E O ●

    lf : {Γ : Ctx} {A : Set}
      → {β : Tree₂ Γ A} {E : Eqv (Σ↓ Γ) A}
      → {n : ℕ} (f : Frm Γ A β E n)
      → (C : Cell Γ A β E n f)
      → Tree Γ A β E (S n) (f ∣ η f C ▸ C)
    nd : {Γ : Ctx} {A : Set}
      → {β : Tree₂ Γ A} {E : Eqv (Σ↓ Γ) A}
      → {n : ℕ} (f : Frm Γ A β E n)
      → (σ : Tree Γ A β E n f) (τ : Cell Γ A β E n f)
      → (δ : (p : Pos σ) → Tree Γ A β E n (Typ σ p))
      → (ε : (p : Pos σ) → Tree Γ A β E (S n) (Typ σ p ∣ δ p ▸ Inh σ p))
      → (θ : Cell Γ A β E (S n) (f ∣ σ ▸ τ))
      → Tree Γ A β E (S n) (f ∣ μ f σ δ ▸ τ)


  η = {!!}
  μ = {!!}

  Cell = {!!}
  Pos = {!!}
  Typ = {!!}
  Inh = {!!}
