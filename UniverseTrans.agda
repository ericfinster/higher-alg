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

  μ-frm : {n : ℕ} (f : Frm n) (σ : Tree {n} f) 
    → (δ : (p : Pos σ) → Tree {n} (Typ σ p))
    → (ε : (p : Pos σ) → Tree {S n} (Typ σ p , δ p , Inh σ p))
    → Frm n

  μ : {n : ℕ} (f : Frm n) (σ : Tree {n} f) 
    → (δ : (p : Pos σ) → Tree {n} (Typ σ p))
    → (ε : (p : Pos σ) → Tree {S n} (Typ σ p , δ p , Inh σ p))
    → Tree (μ-frm f σ δ ε)

  μ-trans : {n : ℕ} (f : Frm n) (σ : Tree {n} f) 
    → (δ : (p : Pos σ) → Tree {n} (Typ σ p))
    → (ε : (p : Pos σ) → Tree {S n} (Typ σ p , δ p , Inh σ p))
    → Cell {n} f
    → Cell {n} (μ-frm f σ δ ε)

  γ : {n : ℕ} (f : Frm n) (σ : Tree {n} f) (τ : Cell {n} f)
    → (θ : Tree {S n} (f , σ , τ))
    → (δ : (p : Pos σ) → Tree {n} (Typ σ p))
    → (ε : (p : Pos σ) → Tree {S n} (Typ σ p , δ p , Inh σ p))
    → Tree {S n} (μ-frm f σ δ ε , μ f σ δ ε , μ-trans f σ δ ε τ)

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

  postulate
  
    -- μ laws
    μ-frm-unit-r : {n : ℕ} (f : Frm n) (σ : Tree {n} f)
      → μ-frm f σ (λ p → η (Typ σ p) (Inh σ p)) (λ p → lf (Typ σ p) (Inh σ p)) ↦ f
    {-# REWRITE μ-frm-unit-r #-}

    μ-unit-r : {n : ℕ} (f : Frm n) (σ : Tree {n} f) 
      → μ f σ (λ p → η (Typ σ p) (Inh σ p)) (λ p → lf (Typ σ p) (Inh σ p)) ↦ σ
    {-# REWRITE μ-unit-r #-}

    μ-trans-unit-r : {n : ℕ} (f : Frm n) (σ : Tree {n} f) (τ : Cell {n} f)
      → μ-trans f σ (λ p → η (Typ σ p) (Inh σ p)) (λ p → lf (Typ σ p) (Inh σ p)) τ ↦ τ 
    {-# REWRITE μ-trans-unit-r #-}
    
  η {O} unit A = cns A (λ _ → nil)
  η {S n} (f , σ , τ) θ = 
    let η-dec p = η (Typ σ p) (Inh σ p)
        lf-dec p = lf (Typ σ p) (Inh σ p)
    in nd f σ τ θ η-dec lf-dec

  μ-frm {O} f σ δ ε = unit
  μ-frm {S n} (f , .(η f τ) , τ) (lf .f .τ) δ₁ ε₁ = f , η f τ , τ
  μ-frm {S n} (._ , ._ , ._) (nd f σ τ θ δ₀ ε₀) δ₁ ε₁ =
    let δ₀' p = {!!}
    in μ-frm f σ δ₀ {!!} , μ f σ δ₀ {!!} , μ-trans f σ δ₀ {!!} τ

  -- Okay, I think I understand the idea: it's that in the recursive
  -- call, you should modify δ₀ and ε₀ by a multiplicaiton ...
  
  μ {O} unit nil δ ε = nil
  μ {O} unit (cns A B) δ ε = {!!}
  μ {S n} (f , .(η f τ) , τ) (lf .f .τ) δ₁ ε₁ = lf f τ
  μ {S n} (._ , ._ , ._) (nd f σ τ θ δ₀ ε₀) δ₁ ε₁ =
    let w = δ₁ (inl unit)
        δ₁' p q = δ₁ (inr (p , q))
        ε₁' p q = ε₁ (inr (p , q))
        -- Shouldn't we have to modify δ₀ as well then?
        ε₀' p = μ (Typ σ p , δ₀ p , Inh σ p) (ε₀ p) (δ₁' p) (ε₁' p)
    in {! γ f σ τ w δ₀ ε₀'!}

  -- Here's another possibility: because we now use the extra data
  -- when computing μ, it's possible that γ should no longer just
  -- be multiplication in the free monad.  Rather, it should carry
  -- along the higher information as well, calling back to μ when
  -- it arrives at a leaf.  Could this allow for its type to be
  -- more flexible????

  μ-trans = {!!}
  
  γ = {!!}

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

