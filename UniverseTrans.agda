{-# OPTIONS --without-K --rewriting --type-in-type #-}

open import Base

module UniverseTrans where

  --
  --  Basic Signature
  --

  Frm : ℕ → Set
  Cell : {n : ℕ} → Frm n → Set
  
  data Tree : {n : ℕ} → Frm n → Set
  Pos : {n : ℕ} {f : Frm n} (σ : Tree f) → Set

  Typ : {n : ℕ} {f : Frm n} (σ : Tree f) (p : Pos σ) → Frm n
  Inh : {n : ℕ} {f : Frm n} (σ : Tree f) (p : Pos σ) → Cell (Typ σ p)

  Frm↓ : {n : ℕ} → Frm n → Set
  Cell↓ : {n : ℕ} {f : Frm n} → Frm↓ f → Cell f → Set
  
  data Tree↓ : {n : ℕ} {f : Frm n} → Frm↓ f → Tree f → Set
  -- Pos↓ : {n : ℕ} {f : Frm n} {f↓ : Frm↓ f} {σ : Tree f}
  --   → (σ↓ : Tree↓ f↓ σ) → Set

  --
  --  Equivalences
  --

  record Eqv (A B : Set) : Set where
    field
      Rel : A → B → Set
      To : A → B
      ToRel : (a : A) → Rel a (To a)

  open Eqv

  --
  --  Base definitions
  --
  
  Frm O = ⊤
  Frm (S n) = Σ (Frm n) (λ f →
    Tree {n} f × Cell {n} f)
  
  Cell {O} unit = Set
  Cell {S n} (f , σ , τ) =
    (f↓ : Frm↓ f) → Eqv (Tree↓ f↓ σ) (Cell↓ f↓ τ) 

  η : {n : ℕ} (f : Frm n)
    → Cell {n} f
    → Tree {n} f
  η = {!!}

  μ-frm : {n : ℕ} (f : Frm n) (σ : Tree {n} f) 
    → (δ : (p : Pos σ) → Tree {n} (Typ σ p))
    → (ε : (p : Pos σ) → Tree {S n} (Typ σ p , δ p , Inh σ p))
    → Frm n
  μ-frm = {!!}

  μ : {n : ℕ} (f : Frm n) (σ : Tree {n} f) 
    → (δ : (p : Pos σ) → Tree {n} (Typ σ p))
    → (ε : (p : Pos σ) → Tree {S n} (Typ σ p , δ p , Inh σ p))
    → Tree (μ-frm f σ δ ε)
  μ = {!!}

  μ-trans : {n : ℕ} (f : Frm n) (σ : Tree {n} f) 
    → (δ : (p : Pos σ) → Tree {n} (Typ σ p))
    → (ε : (p : Pos σ) → Tree {S n} (Typ σ p , δ p , Inh σ p))
    → Cell {n} f
    → Cell {n} (μ-frm f σ δ ε)
  μ-trans = {!!}

  data Tree where
  
    nil : Tree {O} unit
    cns : (A : Set) (B : A → Tree {O} unit)
      → Tree {O} unit

    lf : {n : ℕ} (f : Frm n) (τ : Cell {n} f)
      → Tree {S n} (f , η f τ , τ) 
    nd : {n : ℕ} (f : Frm n)
      → (σ : Tree {n} f) (τ : Cell {n} f)
      → (θ : Cell {S n} (f , σ , τ))
      → (δ : (p : Pos σ) → Tree {n} (Typ σ p))
      → (ε : (p : Pos σ) → Tree {S n} (Typ σ p , δ p , Inh σ p))
      → Tree {S n} (μ-frm f σ δ ε , μ f σ δ ε , μ-trans f σ δ ε τ)
    
  Pos nil = ⊥
  Pos (cns A B) = ⊤ ⊔ Σ A (λ a → Pos (B a))
  Pos (lf f τ) = ⊥
  Pos (nd f σ τ θ δ ε) = ⊤ ⊔ Σ (Pos σ) (λ p → Pos (ε p))
  
  Typ nil ()
  Typ (cns A B) (inl unit) = unit
  Typ (cns A B) (inr (p , q)) = Typ (B p) q
  Typ (lf f τ) ()
  Typ (nd f σ τ θ δ ε) (inl unit) = f , σ , τ
  Typ (nd f σ τ θ δ ε) (inr (p , q)) = Typ (ε p) q
  
  Inh nil ()
  Inh (cns A B) (inl unit) = A
  Inh (cns A B) (inr (p , q)) = Inh (B p) q
  Inh (lf f τ) ()
  Inh (nd f σ τ θ δ ε) (inl unit) = θ
  Inh (nd f σ τ θ δ ε) (inr (p , q)) = Inh (ε p) q

  --
  --  Total definitions
  --
  
  Frm↓ {O} unit = ⊤
  Frm↓ {S n} (f , σ , τ) = Σ (Frm↓ f) (λ f↓ →
    Tree↓ f↓ σ × Cell↓ f↓ τ)
  
  Cell↓ {O} unit A = A
  Cell↓ {S n} {f , σ , τ} (f↓ , σ↓ , τ↓) E =
    Rel (E f↓) σ↓ τ↓

  data Tree↓ where

