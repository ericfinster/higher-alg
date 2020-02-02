{-# OPTIONS --without-K --rewriting --type-in-type --no-positivity #-}

open import Base

module Universe where

  --
  --  Basic Signature 
  --
  
  data Frm : ℕ → Set
  data Tree : {n : ℕ} → Frm n → Set
  data Pos : {n : ℕ} {f : Frm n} (σ : Tree f) → Set

  Cell : {n : ℕ} → Frm n → Set

  Typ : {n : ℕ} {f : Frm n} (σ : Tree f) (p : Pos σ) → Frm n
  Inh : {n : ℕ} {f : Frm n} (σ : Tree f) (p : Pos σ) → Cell (Typ σ p)

  data Frm↓ : {n : ℕ} → Frm n → Set 
  data Tree↓ : {n : ℕ} {f : Frm n} (f↓ : Frm↓ f) → Tree f → Set where
  data Pos↓ : {n : ℕ} {f : Frm n} {f↓ : Frm↓ f} {σ : Tree f} → Tree↓ f↓ σ → Pos σ → Set where
  
  Cell↓ : {n : ℕ} {f : Frm n} (f↓ : Frm↓ f) (A : Cell f) → Set

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

  --
  --  Base definitions
  --
  
  infixl 30 _∣_▸_ 

  data Frm where
    _▸_ : (Γ : Ctx) (A : Set) → Frm O
    _∣_▸_ : {n : ℕ} (f : Frm n)
      → (σ : Tree f) (τ : Cell f)
      → Frm (S n)

  record Eqv (Γ : Ctx) (A : Set) : Set where
    field
      EqvRel : Σ↓ Γ → A → Set
      EqvTo : Σ↓ Γ → A

  open Eqv

  record Coh {n : ℕ} (f : Frm n) (σ : Tree f) (τ : Cell f) : Set where
    inductive
    field
      CohRel : {f↓ : Frm↓ f} → Tree↓ f↓ σ → Cell↓ f↓ τ → Set
      
  open Coh

  Cell (Γ ▸ A) = Eqv Γ A
  Cell (f ∣ σ ▸ τ) = Coh f σ τ

  η-ctx : (A : Set) → Ctx

  -- Yikes! Don't immediately see what's wrong with what I've done,
  -- but have to check the termination here ....
  {-# TERMINATING #-}
  μ-ctx : (Γ : Ctx) 
    → (δ : (p : CtxPos Γ) → Ctx)
    → (ε : (p : CtxPos Γ) → Tree (δ p ▸ CtxTyp Γ p))
    → Ctx

  γ-ctx : (Γ : Ctx) (δ : Σ↓ Γ  → Ctx) → Ctx

  γ-ctx-fst : (Γ : Ctx)
    → (δ : Σ↓ Γ  → Ctx) 
    → (s : Σ↓ (γ-ctx Γ δ))
    → Σ↓ Γ

  γ-ctx-snd : (Γ : Ctx)
    → (δ : Σ↓ Γ  → Ctx) 
    → (s : Σ↓ (γ-ctx Γ δ))
    → Σ↓ (δ (γ-ctx-fst Γ δ s))

  transp-tree : (Γ : Ctx) (A : Set)
    → (σ : Tree (Γ ▸ A))
    → Σ↓ Γ → A

  transp-tree-lcl : (Γ : Ctx)
    → (δ : CtxPos Γ → Ctx)
    → (ε : (p : CtxPos Γ) → Tree (δ p ▸ CtxTyp Γ p))
    → Σ↓ (μ-ctx Γ δ ε)
    → Σ↓ Γ

  η : {n : ℕ} (f : Frm n) (A : Cell f)
    → Tree f

  μ : {n : ℕ} (f : Frm n) (σ : Tree f) 
    → (δ : (p : Pos σ) → Tree (Typ σ p))
    → Tree f

  data Tree where
  
    lf-ctx : (A : Set) → Tree (η-ctx A ▸ A)
    nd-ctx : (Γ : Ctx) (A : Set) (E : Eqv Γ A)
      → (δ : (p : CtxPos Γ) → Ctx)
      → (ε : (p : CtxPos Γ) → Tree (δ p ▸ CtxTyp Γ p))
      → Tree (μ-ctx Γ δ ε ▸ A)

    lf : {n : ℕ} (f : Frm n) (τ : Cell f) → Tree (f ∣ η f τ ▸ τ)
    nd : {n : ℕ} (f : Frm n) (σ : Tree f) (τ : Cell f) (C : Coh f σ τ)
       → (δ : (p : Pos σ) → Tree (Typ σ p))
       → (ε : (p : Pos σ) → Tree (Typ σ p ∣ δ p ▸ Inh σ p))
       → Tree (f ∣ μ f σ δ ▸ τ)
  
  data Pos where
  
    nd-ctx-here : {Γ : Ctx} {A : Set} {E : Eqv Γ A}
      → {δ : (p : CtxPos Γ) → Ctx}
      → {ε : (p : CtxPos Γ) → Tree (δ p ▸ CtxTyp Γ p)}
      → Pos (nd-ctx Γ A E δ ε)
    nd-ctx-there : {Γ : Ctx} {A : Set} {E : Eqv Γ A}
      → {δ : (p : CtxPos Γ) → Ctx}
      → {ε : (p : CtxPos Γ) → Tree (δ p ▸ CtxTyp Γ p)}
      → (p : CtxPos Γ) (q : Pos (ε p))
      → Pos (nd-ctx Γ A E δ ε)

    nd-here : {n : ℕ} {f : Frm n} {σ : Tree f} {τ : Cell f} {C : Coh f σ τ}
       → {δ : (p : Pos σ) → Tree (Typ σ p)}
       → {ε : (p : Pos σ) → Tree (Typ σ p ∣ δ p ▸ Inh σ p)}
       → Pos (nd f σ τ C δ ε) 
    nd-there : {n : ℕ} {f : Frm n} {σ : Tree f} {τ : Cell f} {C : Coh f σ τ}
       → {δ : (p : Pos σ) → Tree (Typ σ p)}
       → {ε : (p : Pos σ) → Tree (Typ σ p ∣ δ p ▸ Inh σ p)}
       → (p : Pos σ) (q : Pos (ε p))
       → Pos (nd f σ τ C δ ε) 

  Typ ._ (nd-ctx-here {Γ} {A}) = Γ ▸ A
  Typ ._ (nd-ctx-there p q) = Typ _ q
  Typ ._ (nd-here {n} {f} {σ} {τ}) = f ∣ σ ▸ τ
  Typ ._ (nd-there p q) = Typ _ q
  
  Inh ._ (nd-ctx-here {E = E}) = E
  Inh ._ (nd-ctx-there p q) = Inh _ q
  Inh ._ (nd-here {C = C}) = C
  Inh ._ (nd-there p q) = Inh _ q

  η-ctx A = cns A (λ _ → nil)

  μ-ctx nil δ ε = nil
  μ-ctx (cns A B) δ ε = 
    let Γ' = δ (cns-here A B)
        a s = transp-tree Γ' A (ε (cns-here A B)) s
        δ' s t = δ (cns-there A B (a s) t)
        ε' s t = ε (cns-there A B (a s) t)
        ϕ s = μ-ctx (B (a s)) (δ' s) (ε' s)
    in γ-ctx Γ' ϕ

  γ-ctx nil δ = δ nil↓
  γ-ctx (cns A B) δ = cns A (λ a → γ-ctx (B a) (λ b↓ → δ (cns↓ a b↓)))

  γ-ctx-fst nil δ s = nil↓
  γ-ctx-fst (cns A B) δ (cns↓ a s) =
    cns↓ a (γ-ctx-fst (B a) (λ b↓ → δ (cns↓ a b↓)) s)

  γ-ctx-snd nil δ s = s
  γ-ctx-snd (cns A B) δ (cns↓ a s) =
    γ-ctx-snd (B a) (λ b↓ → δ (cns↓ a b↓)) s

  transp-tree .(cns A (λ _ → nil)) A (lf-ctx .A) (cns↓ a _) = a
  transp-tree .(μ-ctx Γ δ ε) A (nd-ctx Γ .A E δ ε) s =
    EqvTo E (transp-tree-lcl Γ δ ε s)

  transp-tree-lcl nil δ ε s = s
  transp-tree-lcl (cns A B) δ ε s = 
    let Γ' = δ (cns-here A B)
        a s = transp-tree Γ' A (ε (cns-here A B)) s
        δ' s t = δ (cns-there A B (a s) t)
        ε' s t = ε (cns-there A B (a s) t)
        ϕ s = μ-ctx (B (a s)) (δ' s) (ε' s)
        s' = γ-ctx-fst Γ' ϕ s
    in cns↓ (a s') (transp-tree-lcl (B (a s')) (δ' s') (ε' s') (γ-ctx-snd Γ' ϕ s))

  postulate

    -- μ-ctx laws
    μ-ctx-unit-r : (Γ : Ctx)
      → μ-ctx Γ (λ p → η-ctx (CtxTyp Γ p)) (λ p → lf-ctx (CtxTyp Γ p)) ↦ Γ
    {-# REWRITE μ-ctx-unit-r #-}

    -- μ laws
    μ-unit-r : {n : ℕ} (f : Frm n) (σ : Tree f) 
      → μ f σ (λ p → η (Typ σ p) (Inh σ p)) ↦ σ
    {-# REWRITE μ-unit-r #-}


  η (Γ ▸ A) C = 
    let η-ctx-dec p = η-ctx (CtxTyp Γ p)
        lf-ctx-dec p = lf-ctx (CtxTyp Γ p)
     in nd-ctx Γ A C η-ctx-dec lf-ctx-dec
  η (f ∣ σ ▸ τ) C = 
    let η-dec p = η (Typ σ p) (Inh σ p)
        lf-dec p = lf (Typ σ p) (Inh σ p)
    in nd f σ τ C η-dec lf-dec

  μ = {!!}

  --
  --  Total definitions
  --

  infixl 30 _∥_▸_ 

  data Frm↓ where
    _▸▸_ : {Γ : Ctx} {A : Set}
      → (g : Σ↓ Γ) (a : A)
      → Frm↓ (Γ ▸ A)
    _∥_▸_ : {n : ℕ} {f : Frm n} {σ : Tree f} {τ : Cell f}
      → (f↓ : Frm↓ f) (σ↓ : Tree↓ f↓ σ) (t : Cell↓ f↓ τ)
      → Frm↓ (f ∣ σ ▸ τ)

  Cell↓ (g ▸▸ a) A = EqvRel A g a
  Cell↓ (f↓ ∥ σ↓ ▸ τ↓) A = CohRel A σ↓ τ↓ 
