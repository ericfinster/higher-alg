{-# OPTIONS --without-K --rewriting --type-in-type --no-positivity #-}

open import Base

module UniverseTest where

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
    inductive
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

  Frm↓ {O} unit = ⊤
  Frm↓ {S n} (f , σ , τ) = Σ (Frm↓ f) (λ f↓ →
    Tree↓ f↓ σ × Cell↓ f↓ τ)
  
  Cell↓ {O} unit A = A
  Cell↓ {S n} {f , σ , τ} (f↓ , σ↓ , τ↓) E =
    Rel (E f↓) σ↓ τ↓

  η : {n : ℕ} (f : Frm n)
    → Cell {n} f
    → Tree {n} f

  {-# TERMINATING #-}
  μ : {n : ℕ} (f : Frm n) (σ : Tree {n} f) 
    → (δ : (p : Pos σ) → Tree {n} (Typ σ p))
    → (ε : (p : Pos σ) → Tree {S n} (Typ σ p , δ p , Inh σ p))
    → Tree f

  μ-pos : {n : ℕ} (f : Frm n) (σ : Tree {n} f) 
    → (δ : (p : Pos σ) → Tree {n} (Typ σ p))
    → (ε : (p : Pos σ) → Tree {S n} (Typ σ p , δ p , Inh σ p))    
    → (p : Pos σ) (q : Pos (δ p))
    → Pos (μ f σ δ ε)

  μ-pos-fst : {n : ℕ} (f : Frm n) (σ : Tree {n} f) 
    → (δ : (p : Pos σ) → Tree {n} (Typ σ p))
    → (ε : (p : Pos σ) → Tree {S n} (Typ σ p , δ p , Inh σ p))    
    → Pos (μ f σ δ ε) → Pos σ

  μ-pos-snd : {n : ℕ} (f : Frm n) (σ : Tree {n} f) 
    → (δ : (p : Pos σ) → Tree {n} (Typ σ p))
    → (ε : (p : Pos σ) → Tree {S n} (Typ σ p , δ p , Inh σ p))    
    → (p : Pos (μ f σ δ ε)) → Pos (δ (μ-pos-fst f σ δ ε p))

  γ-ctx : (Γ : Tree unit)
    → (δ : (s : Tree↓ {O} unit Γ) → Tree unit)
    → (ε : (s : Tree↓ {O} unit Γ) (p : Pos (δ s)) → Tree (Typ (δ s) p))
    → (ζ : (s : Tree↓ {O} unit Γ) (p : Pos (δ s)) → Tree {S O} (Typ (δ s) p , ε s p , Inh (δ s) p))
    → Tree unit

  γ : {n : ℕ} (f : Frm n) (σ : Tree {n} f) (τ : Cell {n} f)
    → (θ : Tree {S n} (f , σ , τ))
    → (δ₀ : (p : Pos σ) → Tree {n} (Typ σ p))
    → (ε₀ : (p : Pos σ) → Tree {S n} (Typ σ p , δ₀ p , Inh σ p))
    → (δ₁ : (p : Pos σ) (q : Pos (ε₀ p)) → Tree (Typ (ε₀ p) q))
    → (ε₁ : (p : Pos σ) (q : Pos (ε₀ p)) → Tree (Typ (ε₀ p) q , δ₁ p q , Inh (ε₀ p) q))
    → Tree {S n} (f , μ f σ δ₀ ε₀ , τ)

  -- Okay.  But now, wasn't the idea that the return type here would be
  -- able exactly to be *modified* by substituting multiplying in the
  -- remainging decorations?  In that way we reflect what is actually happening ...
  -- Yeah, but then we're right back where we started: this will then not give
  -- the right answer for the return type of μ ....

  transport : {n : ℕ} (f : Frm n)
    → (σ : Tree {n} f) (τ : Cell {n} f)
    → (θ : Tree {S n} (f , σ , τ))
    → (f↓ : Frm↓ f) (σ↓ : Tree↓ f↓ σ)
    → Cell↓ f↓ τ

  transport-lcl : {n : ℕ} (f : Frm n) (σ : Tree {n} f) 
    → (δ : (p : Pos σ) → Tree {n} (Typ σ p))
    → (ε : (p : Pos σ) → Tree {S n} (Typ σ p , δ p , Inh σ p))
    → (f↓ : Frm↓ f)
    → Tree↓ f↓ (μ f σ δ ε)
    → Tree↓ f↓ σ

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
      → Tree {S n} (f , μ f σ δ ε , τ)
    
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

  data Tree↓ where

    nil↓ : Tree↓ {O} unit nil
    cns↓ : {A : Set} {B : A → Tree {O} unit}
      → (a : A) (b : Tree↓ {O} unit (B a))
      → Tree↓ {O} unit (cns A B)

  postulate

    μ-unit-r : {n : ℕ} (f : Frm n) (σ : Tree {n} f) 
      → μ f σ (λ p → η (Typ σ p) (Inh σ p)) (λ p → lf (Typ σ p) (Inh σ p)) ↦ σ
    {-# REWRITE μ-unit-r #-}

    μ-pos-typ : {n : ℕ} (f : Frm n) (σ : Tree {n} f) 
      → (δ : (p : Pos σ) → Tree {n} (Typ σ p))
      → (ε : (p : Pos σ) → Tree {S n} (Typ σ p , δ p , Inh σ p))    
      → (p : Pos (μ f σ δ ε))
      → Typ (μ f σ δ ε) p ↦ Typ (δ (μ-pos-fst f σ δ ε p)) (μ-pos-snd f σ δ ε p)
    {-# REWRITE μ-pos-typ #-}

    μ-pos-inh : {n : ℕ} (f : Frm n) (σ : Tree {n} f) 
      → (δ : (p : Pos σ) → Tree {n} (Typ σ p))
      → (ε : (p : Pos σ) → Tree {S n} (Typ σ p , δ p , Inh σ p))    
      → (p : Pos (μ f σ δ ε))
      → Inh (μ f σ δ ε) p ↦ Inh (δ (μ-pos-fst f σ δ ε p)) (μ-pos-snd f σ δ ε p)
    {-# REWRITE μ-pos-inh #-}

    μ-pos-fst-β : {n : ℕ} (f : Frm n) (σ : Tree {n} f) 
      → (δ : (p : Pos σ) → Tree {n} (Typ σ p))
      → (ε : (p : Pos σ) → Tree {S n} (Typ σ p , δ p , Inh σ p))
      → (p : Pos σ) (q : Pos (δ p))
      → μ-pos-fst f σ δ ε (μ-pos f σ δ ε p q) ↦ p 
    {-# REWRITE μ-pos-fst-β #-}

    μ-pos-snd-β : {n : ℕ} (f : Frm n) (σ : Tree {n} f) 
      → (δ : (p : Pos σ) → Tree {n} (Typ σ p))
      → (ε : (p : Pos σ) → Tree {S n} (Typ σ p , δ p , Inh σ p))
      → (p : Pos σ) (q : Pos (δ p))
      → μ-pos-snd f σ δ ε (μ-pos f σ δ ε p q) ↦ q
    {-# REWRITE μ-pos-snd-β #-}

    μ-pos-η : {n : ℕ} (f : Frm n) (σ : Tree {n} f) 
      → (δ : (p : Pos σ) → Tree {n} (Typ σ p))
      → (ε : (p : Pos σ) → Tree {S n} (Typ σ p , δ p , Inh σ p))    
      → (p : Pos (μ f σ δ ε))
      → μ-pos f σ δ ε (μ-pos-fst f σ δ ε p) (μ-pos-snd f σ δ ε p) ↦ p
    {-# REWRITE μ-pos-η #-}


    μ-assoc : {n : ℕ} (f : Frm n) (σ : Tree {n} f) (τ : Cell {n} f)
      → (δ : (p : Pos σ) → Tree {n} (Typ σ p))
      → (ε : (p : Pos σ) → Tree {S n} (Typ σ p , δ p , Inh σ p))
      → (δ' : (p : Pos (μ f σ δ ε)) → Tree (Typ (μ f σ δ ε) p))
      → (ε' : (p : Pos (μ f σ δ ε)) → Tree (Typ (μ f σ δ ε) p , δ' p , Inh (μ f σ δ ε) p))
      → (δ'' : (p₀ : Pos σ) (p₁ : Pos (δ p₀)) (q : Pos (ε' (μ-pos f σ δ ε p₀ p₁))) → Tree (Typ (ε' (μ-pos f σ δ ε p₀ p₁)) q))
      → (ε'' : (p₀ : Pos σ) (p₁ : Pos (δ p₀)) (q : Pos (ε' (μ-pos f σ δ ε p₀ p₁))) → Tree (Typ (ε' (μ-pos f σ δ ε p₀ p₁)) q , δ'' p₀ p₁ q , Inh (ε' (μ-pos f σ δ ε p₀ p₁)) q))
      → μ f (μ f σ δ ε) δ' (λ p → μ (Typ (δ (μ-pos-fst f σ δ ε p)) (μ-pos-snd f σ δ ε p) , δ' p , Inh (δ (μ-pos-fst f σ δ ε p)) (μ-pos-snd f σ δ ε p))
                                    (ε' p)
                                    (λ q → δ'' (μ-pos-fst f σ δ ε p) (μ-pos-snd f σ δ ε p) q)
                                    (λ q → ε'' (μ-pos-fst f σ δ ε p) (μ-pos-snd f σ δ ε p) q))
          ↦
        μ f σ (λ p → μ (Typ σ p) (δ p) (λ q → δ' (μ-pos f σ δ ε p q)) (λ q → ε' (μ-pos f σ δ ε p q)))
              (λ p → γ (Typ σ p) (δ p) (Inh σ p) (ε p)
                     (λ q → δ' (μ-pos f σ δ ε p q))
                     (λ q → ε' (μ-pos f σ δ ε p q)) (δ'' p) (ε'' p))
    -- {-# REWRITE μ-assoc #-}

  -- I see: we need a third pair!  Hmm.  But then they won't be bound in the left hand
  -- side.  Oh, unless δ' and ε' become the multiplications of the additional pair...

  -- γ : {n : ℕ} (f : Frm n) (σ : Tree {n} f) (τ : Cell {n} f)
  --   → (θ : Tree {S n} (f , σ , τ))
  --   → (δ₀ : (p : Pos σ) → Tree {n} (Typ σ p))
  --   → (ε₀ : (p : Pos σ) → Tree {S n} (Typ σ p , δ₀ p , Inh σ p))
  --   → (δ₁ : (p : Pos σ) (q : Pos (ε₀ p)) → Tree (Typ (ε₀ p) q))
  --   → (ε₁ : (p : Pos σ) (q : Pos (ε₀ p)) → Tree (Typ (ε₀ p) q , δ₁ p q , Inh (ε₀ p) q))
  --   → Tree {S n} (f , μ f σ δ₀ ε₀ , τ)

    -- μ-assoc : (f : Frm) (σ : Tree f) (τ : Cell f)
    --   → (δ : (p : Pos σ) → Tree (Typ σ p))
    --   → (ε : (p : Pos σ) → Tree (Typ σ p ∥ δ p ▸ Inh σ p))
    --   → (δ' : (p : Pos (μ f σ δ ε)) → Tree (Typ (δ (μ-pos-fst f σ δ ε p)) (μ-pos-snd f σ δ ε p)))
    --   → (ε' : (p : Pos (μ f σ δ ε)) → Tree (Typ (δ (μ-pos-fst f σ δ ε p)) (μ-pos-snd f σ δ ε p) ∥ δ' p ▸ Inh (δ (μ-pos-fst f σ δ ε p)) (μ-pos-snd f σ δ ε p)))
    --   → μ f (μ f σ δ ε) δ' ε' ↦ μ f σ (λ p → μ (Typ σ p) (δ p) (λ q → δ' (μ-pos f σ δ ε p q)) (λ q → ε' (μ-pos f σ δ ε p q)))
    --                                   (λ p → γ (δ p) (Inh σ p) (ε p) (λ q → δ' (μ-pos f σ δ ε p q)) (λ q → ε' (μ-pos f σ δ ε p q)))
    -- {-# REWRITE μ-assoc #-}


    γ-ctx-unit-right : (Γ : Tree unit)
      → (ε : (s : Tree↓ unit Γ) (p : ⊥) → Tree (Typ nil p))
      → (ζ : (s : Tree↓ unit Γ) (p : ⊥) → Tree (Typ nil p , ε s p , Inh nil p))
      → γ-ctx Γ (λ _ → nil) ε ζ ↦ Γ
    {-# REWRITE γ-ctx-unit-right #-}

  η {O} unit A = cns A (λ _ → nil)
  η {S n} (f , σ , τ) θ = 
    let η-dec p = η (Typ σ p) (Inh σ p)
        lf-dec p = lf (Typ σ p) (Inh σ p)
    in nd f σ τ θ η-dec lf-dec
  
  μ {O} unit nil δ ε = nil
  μ {O} unit (cns A B) δ ε =
    let Γ = δ (inl unit)
        a s = transport {O} unit Γ A (ε (inl unit)) unit s
        B' s = B (a s)
        δ' s p = δ (inr (a s , p))
        ε' s p = ε (inr (a s , p))
    in γ-ctx Γ B' δ' ε'
  μ {S n} (f , .(η f τ) , τ) (lf .f .τ) δ₁ ε₁ = lf f τ
  μ {S n} (._ , ._ , ._) (nd f σ τ θ δ₀ ε₀) δ₁ ε₁ = 
    let w = δ₁ (inl unit)
        δ₁' p q = δ₁ (inr (p , q))
        ε₁' p q = ε₁ (inr (p , q))
    in {! γ f σ τ w δ₀ ε₀ δ₁' ε₁' !}

  μ-pos = {!!}
  μ-pos-fst = {!!}
  μ-pos-snd = {!!}
  
  γ-ctx nil δ ε ζ =
    μ {O} unit (δ nil↓) (λ p → ε nil↓ p) (λ p → ζ nil↓ p)
  γ-ctx (cns A B) δ ε ζ =
    cns A (λ a → γ-ctx (B a) (λ s → δ (cns↓ a s))
                             (λ s p → ε (cns↓ a s) p)
                             (λ s p → ζ (cns↓ a s) p))

  -- γ : {n : ℕ} (f : Frm n) (σ : Tree {n} f) (τ : Cell {n} f)
  --   → (θ : Tree {S n} (f , σ , τ))
  --   → (δ₀ : (p : Pos σ) → Tree {n} (Typ σ p))
  --   → (ε₀ : (p : Pos σ) → Tree {S n} (Typ σ p , δ₀ p , Inh σ p))
  --   → (δ₁ : (p : Pos σ) (q : Pos (ε₀ p)) → Tree (Typ (ε₀ p) q))
  --   → (ε₁ : (p : Pos σ) (q : Pos (ε₀ p)) → Tree (Typ (ε₀ p) q , δ₁ p q , Inh (ε₀ p) q))
  --   → Tree {S n} (f , μ f σ δ₀ ε₀ , τ)
  γ {O} unit ._ A (lf .unit .A) δ₀ ε₀ δ₁ ε₁ =
    μ {S O} (unit , δ₀ (inl unit) , A) (ε₀ (inl unit))
      (λ p → δ₁ (inl unit) p) (λ p → ε₁ (inl unit) p)
      -- Okay, that was the idea: finish multiplication at the leaves ...
  γ {O} unit ._ A (nd .unit Γ .A θ δ ε) δ₀ ε₀ δ₁ ε₁ =

    {!nd unit Γ A θ!}

  -- So, here we will need the associativity of μ.
  
-- Goal: Tree (unit , μ unit (μ unit Γ δ ε) δ₀ ε₀ , A)
-- Have: (δ₂ : (p : Pos Γ) → Tree (Typ Γ p))
--       (ε₂ : (p : Pos Γ) → Tree (Typ Γ p , δ₂ p , Inh Γ p)) →
--       Tree (unit , μ unit Γ δ₂ ε₂ , A)


  γ {S n} ._ ._ ._ (lf (f , σ₀ , τ₀) τ₁) δ₀ ε₀ δ₁ ε₁ = {!!}
    -- It looks like γ-unit law should take care of this one ...
  γ {S n} ._ ._ ._ (nd (f , σ₀ , τ₀) θ σ₁ τ₁ δ ε) δ₀ ε₀ δ₁ ε₁ =
    {!nd (f , σ₀ , τ₀) θ σ₁ ? ? ?!}
    -- Wow, and here it really looks like some kind of associativity
    -- could possibly save us.  Have to be very careful about the
    -- types, but maybe you will make it out alive.

  -- γ .f .(η f τ) .τ (lf f τ) ϕ ψ = ψ (η-pos f τ)
  -- γ .f .(μ f σ δ) .τ (nd f σ τ α δ ε) ϕ ψ =
  --   let ϕ' p q = ϕ (μ-pos f σ δ p q)
  --       ψ' p q = ψ (μ-pos f σ δ p q)
  --       δ' p = μ (Typ f σ p) (δ p) (ϕ' p)
  --       ε' p = γ (Typ f σ p) (δ p) (Inh f σ p) (ε p) (ϕ' p) (ψ' p)
  --   in nd f σ τ α δ' ε'
  
  -- Interesting.  Here we exposed the equivalence.  Maybe this
  -- will let you directly apply the transport somewhere in order
  -- to fix the types...

  -- This would kind of make sense, as you expect to use the equivalence
  -- for gamma in the lowest dimension as it should correspond to using
  -- the transport...

  -- transport : {n : ℕ} (f : Frm n)
  --   → (σ : Tree {n} f) (τ : Cell {n} f)
  --   → (θ : Tree {S n} (f , σ , τ))
  --   → (f↓ : Frm↓ f) (σ↓ : Tree↓ f↓ σ)
  --   → Cell↓ f↓ τ
  transport {O} unit ._ A (lf .unit .A) unit (cns↓ a nil↓) = a
  transport {O} unit .(μ unit Γ δ ε) A (nd .unit Γ .A θ δ ε) unit σ↓ =
    To (θ unit) (transport-lcl unit Γ δ ε unit σ↓)
  transport {S n} f σ τ θ f↓ σ↓ = {!!}

  transport-lcl = {!!}

