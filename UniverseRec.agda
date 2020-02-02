{-# OPTIONS --without-K --rewriting --type-in-type #-}

open import Base

module UniverseRec where

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
  Tree↓ : {n : ℕ} {f : Frm n} → Frm↓ f → Tree f → Set

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
      Rel : A → B → Set
      To : A → B
      ToRel : (a : A) → Rel a (To a)

  open Eqv
  
  --
  --  Base Definitions
  --
  
  Frm O = ⊤
  Frm (S O) = Ctx × Set
  Frm (S (S n)) = Σ (Frm (S n)) (λ f → Tree {S n} f × Cell {S n} f)

  Cell {O} _ = ⊤
  Cell {S O} (Γ , A) = Eqv (Σ↓ Γ) A
  Cell {S (S n)} (f , σ , τ) =
    (f↓ : Frm↓ {S n} f) → Eqv (Tree↓ f↓ σ) (Cell↓ f↓ τ)


  η-ctx : (A : Set) → Ctx
  η-ctx = {!!}

  μ-ctx : (Γ : Ctx) 
    → (δ : (p : CtxPos Γ) → Ctx)
    → (ε : (p : CtxPos Γ) → Tree {S O} (δ p , CtxTyp Γ p))
    → Ctx
  μ-ctx = {!!}

  η : {n : ℕ} (f : Frm (S n)) (A : Cell {S n} f)
    → Tree {S n} f
  η = {!!}
  
  μ : {n : ℕ} (f : Frm (S n)) (σ : Tree {S n} f) 
    → (δ : (p : Pos σ) → Tree {S n} (Typ σ p))
    → Tree {S n} f
  μ = {!!}
  
  γ : {n : ℕ} {f : Frm (S n)} (σ : Tree {S n} f) (τ : Cell {S n} f)
    → (ρ : Tree {S (S n)} (f , σ , τ)) 
    → (δ : (p : Pos σ) → Tree {S n} (Typ σ p))
    → (ε : (p : Pos σ) → Tree {S (S n)} (Typ σ p , δ p , Inh σ p))
    → Tree {S (S n)} (f , μ f σ δ , τ)
  γ = {!!}

  data Tree where

    lf-ctx : (A : Set) → Tree {S O} (η-ctx A , A)
    nd-ctx : (Γ : Ctx) (A : Set) (E : Eqv (Σ↓ Γ) A)
      → (δ : (p : CtxPos Γ) → Ctx)
      → (ε : (p : CtxPos Γ) → Tree {S O} (δ p , CtxTyp Γ p))
      → Tree {S O} (μ-ctx Γ δ ε , A)

    lf : {n : ℕ} (f : Frm (S n)) (τ : Cell {S n} f)
      → Tree {S (S n)} (f , η f τ , τ)
    nd : {n : ℕ} (f : Frm (S n))
       → (σ : Tree {S n} f) (τ : Cell {S n} f)
       → Cell {S (S n)} (f , σ , τ)
       → (δ : (p : Pos σ) → Tree {S n} (Typ σ p))
       → (ε : (p : Pos σ) → Tree {S (S n)} (Typ σ p , δ p , Inh σ p))
       → Tree {S (S n)} (f , μ f σ δ , τ)

  Pos = {!!}

  Typ = {!!}
  Inh = {!!}


  --
  --  Total Definitions
  --

  Frm↓ {O} _ = ⊤
  Frm↓ {S O} (Γ , A) = Σ↓ Γ × A
  Frm↓ {S (S n)} (f , σ , τ) =
    Σ (Frm↓ {S n} f) (λ f↓ →
    Tree↓ f↓ σ × Cell↓ f↓ τ)

  Cell↓ {O} {_} _ _ = ⊤
  Cell↓ {S O} {Γ , A} (g , a) E =
    Rel E g a
  Cell↓ {S (S n)} {f , σ , τ} (f↓ , σ↓ , τ↓) C =
    Rel (C f↓) σ↓ τ↓ 
  
  Tree↓ = {!!}
