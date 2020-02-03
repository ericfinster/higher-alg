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
  
  data Tree↓ : {n : ℕ} {f : Frm n} → Frm↓ f → Tree f → Set
  Pos↓ : {n : ℕ} {f : Frm n} {f↓ : Frm↓ f} {σ : Tree f}
    → (σ↓ : Tree↓ f↓ σ) → Set
  
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

  -- Yikes! Don't immediately see what's wrong with what I've done,
  -- but have to check the termination here ....
  {-# TERMINATING #-}
  μ-ctx : (Γ : Ctx) 
    → (δ : (p : CtxPos Γ) → Ctx)
    → (ε : (p : CtxPos Γ) → Tree {S O} (δ p , CtxTyp Γ p))
    → Ctx

  transp-tree : (Γ : Ctx) (A : Set)
    → (σ : Tree {S O} (Γ , A))
    → Σ↓ Γ → A

  transp-tree-lcl : (Γ : Ctx)
    → (δ : CtxPos Γ → Ctx)
    → (ε : (p : CtxPos Γ) → Tree {S O} (δ p , CtxTyp Γ p))
    → Σ↓ (μ-ctx Γ δ ε)
    → Σ↓ Γ

  η : {n : ℕ} (f : Frm (S n)) (A : Cell {S n} f)
    → Tree {S n} f

  η-pos : {n : ℕ} (f : Frm (S n)) (τ : Cell {S n} f)
    → Pos (η f τ)

  μ : {n : ℕ} (f : Frm (S n)) (σ : Tree {S n} f) 
    → (δ : (p : Pos σ) → Tree {S n} (Typ σ p))
    → Tree {S n} f

  μ-pos : {n : ℕ} (f : Frm (S n)) (σ : Tree {S n} f) 
    → (δ : (p : Pos σ) → Tree {S n} (Typ σ p))
    → (p : Pos σ) (q : Pos (δ p))
    → Pos (μ f σ δ)
  
  μ-pos-fst : {n : ℕ} (f : Frm (S n)) (σ : Tree {S n} f) 
    → (δ : (p : Pos σ) → Tree {S n} (Typ σ p))
    → Pos (μ f σ δ) → Pos σ
  
  μ-pos-snd : {n : ℕ} (f : Frm (S n)) (σ : Tree {S n} f) 
    → (δ : (p : Pos σ) → Tree {S n} (Typ σ p))
    → (p : Pos (μ f σ δ)) → Pos (δ (μ-pos-fst f σ δ p))

  γ-eqv : (Γ : Ctx) (A : Set)
    → (σ : Tree {S O} (Γ , A))
    → (δ : (p : CtxPos Γ) → Ctx)
    → (ε : (p : CtxPos Γ) → Tree {S O} (δ p , CtxTyp Γ p))
    → Tree {S O} (μ-ctx Γ δ ε , A)
  
  γ : {n : ℕ} {f : Frm (S n)} (σ : Tree {S n} f) (τ : Cell {S n} f)
    → (ρ : Tree {S (S n)} (f , σ , τ)) 
    → (δ : (p : Pos σ) → Tree {S n} (Typ σ p))
    → (ε : (p : Pos σ) → Tree {S (S n)} (Typ σ p , δ p , Inh σ p))
    → Tree {S (S n)} (f , μ f σ δ , τ)

  γ-pos-inl : {n : ℕ} {f : Frm (S n)}
    → (σ : Tree {S n} f) (τ : Cell {S n} f)
    → (ρ : Tree {S (S n)} (f , σ , τ))
    → (δ : (p : Pos σ) → Tree {S n} (Typ σ p))
    → (ε : (p : Pos σ) → Tree {S (S n)} (Typ σ p , δ p , Inh σ p))
    → Pos ρ → Pos (γ σ τ ρ δ ε)

  γ-pos-inr : {n : ℕ} {f : Frm (S n)}
    → (σ : Tree {S n} f) (τ : Cell {S n} f)
    → (ρ : Tree {S (S n)} (f , σ , τ))
    → (δ : (p : Pos σ) → Tree {S n} (Typ σ p))
    → (ε : (p : Pos σ) → Tree {S (S n)} (Typ σ p , δ p , Inh σ p))
    → (p : Pos σ) (q : Pos (ε p))
    → Pos (γ σ τ ρ δ ε)

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
       → (C : Cell {S (S n)} (f , σ , τ))
       → (δ : (p : Pos σ) → Tree {S n} (Typ σ p))
       → (ε : (p : Pos σ) → Tree {S (S n)} (Typ σ p , δ p , Inh σ p))
       → Tree {S (S n)} (f , μ f σ δ , τ)

  Pos (lf-ctx A) = ⊥
  Pos (nd-ctx Γ A E δ ε) = ⊤ ⊔ Σ (CtxPos Γ) (λ p → Pos (ε p))
  Pos (lf f τ) = ⊥
  Pos (nd f σ τ C δ ε) = ⊤ ⊔ Σ (Pos σ) (λ p → Pos (ε p))

  Typ (lf-ctx A) ()
  Typ (nd-ctx Γ A E δ ε) (inl unit) = Γ , A
  Typ (nd-ctx Γ A E δ ε) (inr (p , q)) = Typ (ε p) q
  Typ (lf f τ) ()
  Typ (nd f σ τ C δ ε) (inl unit) = f , σ , τ
  Typ (nd f σ τ C δ ε) (inr (p , q)) = Typ (ε p) q
  
  Inh (lf-ctx A) ()
  Inh (nd-ctx Γ A E δ ε) (inl unit) = E
  Inh (nd-ctx Γ A E δ ε) (inr (p , q)) = Inh (ε p) q
  Inh (lf f τ) ()
  Inh (nd f σ τ C δ ε) (inl unit) = C
  Inh (nd f σ τ C δ ε) (inr (p , q)) = Inh (ε p) q

  η-ctx A = cns A (λ _ → nil)
  
  μ-ctx nil δ ε = nil
  μ-ctx (cns A B) δ ε = 
    let Γ' = δ (cns-here A B)
        a s = transp-tree Γ' A (ε (cns-here A B)) s
        δ' s t = δ (cns-there A B (a s) t)
        ε' s t = ε (cns-there A B (a s) t)
        ϕ s = μ-ctx (B (a s)) (δ' s) (ε' s)
    in γ-ctx Γ' ϕ

  transp-tree .(cns A (λ _ → nil)) A (lf-ctx .A) (cns↓ a _) = a
  transp-tree .(μ-ctx Γ δ ε) A (nd-ctx Γ .A E δ ε) s = 
    To E (transp-tree-lcl Γ δ ε s)

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

    -- YIKES!  This is the one rewrite which really gives me pause.
    -- It says we can definitionally ignore any higher substitutions
    -- into the witnesses of the equivalence.  Need to think about it...
    μ-ctx-invar : (Γ : Ctx) 
      → (δ : (p : CtxPos Γ) → Ctx)
      → (ε : (p : CtxPos Γ) → Tree {S O} (δ p , CtxTyp Γ p))
      → (κ : (p : CtxPos Γ) (q : Pos (ε p)) → Tree {S O} (Typ (ε p) q))
      → μ-ctx Γ δ (λ p → μ (δ p , CtxTyp Γ p) (ε p) (κ p)) ↦ μ-ctx Γ δ ε
    {-# REWRITE μ-ctx-invar #-}

    -- Hmmm.  But if I want this to be justified, then I really should
    -- have also the fillers one dimension higher, which are absent here
    -- because I removed them from the higher dimensional signature.

    -- It seems then that such a rule claims that the result of tree
    -- substitution, while calculated from higher data, does not depend
    -- on modifications to the higher coherences.

    -- I'm not sure this is completely convincing, but here's one
    -- observation about this: it is clear from the definition that
    -- μ-ctx only uses the *function* part of the equivalence, and not
    -- the coherences.  But I'm not sure this is exactly what the rewrite
    -- is actually saying ...
    
    -- μ laws
    μ-unit-r : {n : ℕ} (f : Frm (S n)) (σ : Tree {S n} f) 
      → μ f σ (λ p → η (Typ σ p) (Inh σ p)) ↦ σ
    {-# REWRITE μ-unit-r #-}

  η {O} (Γ , A) E = 
    let η-ctx-dec p = η-ctx (CtxTyp Γ p)
        lf-ctx-dec p = lf-ctx (CtxTyp Γ p)
     in nd-ctx Γ A E η-ctx-dec lf-ctx-dec
  η {S n} (f , σ , τ) C = 
    let η-dec p = η (Typ σ p) (Inh σ p)
        lf-dec p = lf (Typ σ p) (Inh σ p)
    in nd f σ τ C η-dec lf-dec

  η-pos {O} f E = inl unit
  η-pos {S n} f E = inl unit

  μ {O} (.(η-ctx A), A) (lf-ctx .A) κ = lf-ctx A
  μ {O} (.(μ-ctx Γ δ ε) , A) (nd-ctx Γ .A E δ ε) κ =
    let w = κ (inl unit)
        κ' p q = κ (inr (p , q))
        ε' p = μ {O} _ (ε p) (κ' p)
    in  γ-eqv Γ A w δ ε' 
  μ {S n} (f , .(η f τ) , τ) (lf .f .τ) κ = lf f τ
  μ {S n} (f , .(μ f σ δ) , τ) (nd .f σ .τ C δ ε) κ =
    let w = κ (inl unit)
        κ' p q = κ (inr (p , q))
        ϕ p = μ {S n} (Typ σ p , δ p , Inh σ p) (ε p) (κ' p)
    in γ σ τ w δ ϕ

  μ-pos = {!!}
  μ-pos-fst = {!!}
  μ-pos-snd = {!!}

  γ-eqv = {!!}

  γ = {!!}

  γ-pos-inl = {!!}
  γ-pos-inr = {!!}

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

  data Tree↓ where



  -- Is it maybe possible to have Tree↓ as a kind of section?
  -- Tree↓ {O} {f} f↓ ()
  -- Tree↓ {S O} {Γ , A} (g , a) σ' = (p : Pos σ') → {!!}
  -- Tree↓ {S (S n)} {f , σ , τ} f↓ σ' = {!!}

  Pos↓ = {!!}
