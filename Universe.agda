{-# OPTIONS --without-K --rewriting --type-in-type --no-positivity #-}


module Universe where



  -- infixl 30 _∥_▸_  _∣_▸_

  -- data Ctx : Set where
  --   nil : Ctx
  --   cns : (A : Set) (B : A → Ctx) → Ctx

  -- data CtxPos : Ctx → Set where
  --   cns-here : (A : Set) (B : A → Ctx) → CtxPos (cns A B)
  --   cns-there : (A : Set) (B : A → Ctx)
  --     → (a : A) (p : CtxPos (B a))
  --     → CtxPos (cns A B)

  -- CtxTyp : (Γ : Ctx) (p : CtxPos Γ) → Set
  -- CtxTyp .(cns A B) (cns-here A B) = A
  -- CtxTyp .(cns A B) (cns-there A B a p) = CtxTyp (B a) p
  
  -- data Σ↓ : Ctx → Set where
  --   nil↓ : Σ↓ nil
  --   cns↓ : {A : Set} {B : A → Ctx}
  --     → (a : A) (b : Σ↓ (B a))
  --     → Σ↓ (cns A B)

  -- data Frm : Set
  -- data Tree : Frm → Set
  -- data Pos : {f : Frm} (σ : Tree f) → Set

  -- data Frm↓ : Frm → Set 
  -- data Tree↓ : {f : Frm} (f↓ : Frm↓ f) → Tree f → Set where
  -- data Pos↓ : {f : Frm} {f↓ : Frm↓ f} {σ : Tree f} → Tree↓ f↓ σ → Pos σ → Set where

  -- Cell : Frm → Set 
  -- Cell↓ : {f : Frm} (f↓ : Frm↓ f) (A : Cell f) → Set

  -- data Frm where
  --   ● : (Γ : Ctx) (A : Set) → Frm
  --   _∥_▸_ : (f : Frm) (σ : Tree f) (τ : Cell f) → Frm

  -- data Frm↓ where
  --   ∎ : {Γ : Ctx} {A : Set}
  --     → (g : Σ↓ Γ) (a : A)
  --     → Frm↓ (● Γ A)
  --   _∣_▸_ : {f : Frm} {σ : Tree f} {τ : Cell f}
  --     → (f↓ : Frm↓ f) (σ↓ : Tree↓ f↓ σ) (t : Cell↓ f↓ τ)
  --     → Frm↓ (f ∥ σ ▸ τ)

  -- record CtxCell (Γ : Ctx) (A : Set) : Set where
  --   field
  --     CtxRel : Σ↓ Γ → A → Set
  --     eqv-to : Σ↓ Γ → A
  --     wit : (t : Σ↓ Γ) → CtxRel t (eqv-to t)
  --     coh : A → Σ↓ Γ
  --     coh-wit : (a : A) → CtxRel (coh a) a

  -- open CtxCell
  
  -- record EqvCell (f : Frm) (σ : Tree f) (τ : Cell f) : Set where
  --   field
  --     EqvRel : {f↓ : Frm↓ f} → Tree↓ f↓ σ → Cell↓ f↓ τ → Set

  -- open EqvCell
  
  -- Cell (● Γ A) = CtxCell Γ A
  -- Cell (f ∥ σ ▸ τ) = EqvCell f σ τ

  -- Cell↓ {● Γ A} (∎ g a) C = CtxRel C g a
  -- Cell↓ {f ∥ σ ▸ τ} (f↓ ∣ σ↓ ▸ τ↓) C = EqvRel C σ↓ τ↓

  -- Typ : {f : Frm} (σ : Tree f) (p : Pos σ) → Frm
  -- Inh : {f : Frm} (σ : Tree f) (p : Pos σ) → Cell (Typ σ p)

  -- {-# TERMINATING #-}
  -- η : (f : Frm) (A : Cell f)
  --   → Tree f

  -- μ : (f : Frm) (σ : Tree f) 
  --   → (δ : (p : Pos σ) → Tree (Typ σ p))
  --   → Tree f

  -- η-ctx : (A : Set) → Ctx
  -- η-ctx A = cns A (λ _ → nil)
  
  -- μ-ctx : (Γ : Ctx) 
  --   → (δ : (p : CtxPos Γ) → Ctx)
  --   → (ε : (p : CtxPos Γ) → Tree (● (δ p) (CtxTyp Γ p)))
  --   → Ctx

  -- data Tree where
  --   lf-ctx : (A : Set) → Tree (● (η-ctx A) A)
  --   nd-ctx : (Γ : Ctx) (A : Set) (C : CtxCell Γ A)
  --     → (δ : (p : CtxPos Γ) → Ctx)
  --     → (ε : (p : CtxPos Γ) → Tree (● (δ p) (CtxTyp Γ p)))
  --     → Tree (● (μ-ctx Γ δ ε) A)

  --   lf : (f : Frm) (τ : Cell f) → Tree (f ∥ η f τ ▸ τ)
  --   nd : (f : Frm) (σ : Tree f) (τ : Cell f) (C : EqvCell f σ τ)
  --      → (δ : (p : Pos σ) → Tree (Typ σ p))
  --      → (ε : (p : Pos σ) → Tree (Typ σ p ∥ δ p ▸ Inh σ p))
  --      → Tree (f ∥ μ f σ δ ▸ τ)
  
  -- data Pos where

  --   nd-ctx-here : {Γ : Ctx} {A : Set} {C : CtxCell Γ A}
  --     → {δ : (p : CtxPos Γ) → Ctx}
  --     → {ε : (p : CtxPos Γ) → Tree (● (δ p) (CtxTyp Γ p))}
  --     → Pos (nd-ctx Γ A C δ ε)
  --   nd-ctx-there : {Γ : Ctx} {A : Set} {C : CtxCell Γ A}
  --     → {δ : (p : CtxPos Γ) → Ctx}
  --     → {ε : (p : CtxPos Γ) → Tree (● (δ p) (CtxTyp Γ p))}
  --     → (p : CtxPos Γ) (q : Pos (ε p))
  --     → Pos (nd-ctx Γ A C δ ε)

  --   nd-here : {f : Frm} {σ : Tree f} {τ : Cell f} {A : Cell (f ∥ σ ▸ τ)}
  --      → {δ : (p : Pos σ) → Tree (Typ σ p)}
  --      → {ε : (p : Pos σ) → Tree (Typ σ p ∥ δ p ▸ Inh σ p)}
  --      → Pos (nd f σ τ A δ ε) 
  --   nd-there : {f : Frm} {σ : Tree f} {τ : Cell f} {A : Cell (f ∥ σ ▸ τ)}
  --      → {δ : (p : Pos σ) → Tree (Typ σ p)}
  --      → {ε : (p : Pos σ) → Tree (Typ σ p ∥ δ p ▸ Inh σ p)}
  --      → (p : Pos σ) (q : Pos (ε p))
  --      → Pos (nd f σ τ A δ ε) 

  -- Typ ._ (nd-ctx-here {Γ} {A}) = ● Γ A
  -- Typ ._ (nd-ctx-there p q) = Typ _ q
  -- Typ ._ (nd-here {f} {σ} {τ}) = f ∥ σ ▸ τ
  -- Typ ._ (nd-there p q) = Typ _ q
  
  -- Inh ._ (nd-ctx-here {C = C}) = C
  -- Inh ._ (nd-ctx-there p q) = Inh _ q
  -- Inh ._ (nd-here {A = A}) = A
  -- Inh ._ (nd-there p q) = Inh _ q

  -- postulate

  --   -- μ-ctx laws
  --   μ-ctx-unit-r : (Γ : Ctx)
  --     → μ-ctx Γ (λ p → η-ctx (CtxTyp Γ p)) (λ p → lf-ctx (CtxTyp Γ p)) ↦ Γ
  --   {-# REWRITE μ-ctx-unit-r #-}

  --   -- μ laws
  --   μ-unit-r : (f : Frm) (σ : Tree f) 
  --     → μ f σ (λ p → η (Typ σ p) (Inh σ p)) ↦ σ
  --   {-# REWRITE μ-unit-r #-}

  -- γ-ctx : (Γ : Ctx) (δ : Σ↓ Γ  → Ctx) → Ctx
  -- γ-ctx nil δ = δ nil↓
  -- γ-ctx (cns A B) δ = cns A (λ a → γ-ctx (B a) (λ b↓ → δ (cns↓ a b↓)))

  -- γ-lift-fst : (Γ : Ctx)
  --   → (δ : Σ↓ Γ  → Ctx) 
  --   → (s : Σ↓ (γ-ctx Γ δ))
  --   → Σ↓ Γ
  -- γ-lift-fst nil δ s = nil↓
  -- γ-lift-fst (cns A B) δ (cns↓ a s) =
  --   cns↓ a (γ-lift-fst (B a) (λ b↓ → δ (cns↓ a b↓)) s)

  -- γ-lift-snd : (Γ : Ctx)
  --   → (δ : Σ↓ Γ  → Ctx) 
  --   → (s : Σ↓ (γ-ctx Γ δ))
  --   → Σ↓ (δ (γ-lift-fst Γ δ s))
  -- γ-lift-snd nil δ s = s
  -- γ-lift-snd (cns A B) δ (cns↓ a s) =
  --   γ-lift-snd (B a) (λ b↓ → δ (cns↓ a b↓)) s

  -- transp-tree : (Γ : Ctx) (A : Set)
  --   → (σ : Tree (● Γ A))
  --   → Σ↓ Γ → A

  -- lift-tree : (Γ : Ctx)
  --   → (δ : CtxPos Γ → Ctx)
  --   → (ε : (p : CtxPos Γ) → Tree (● (δ p) (CtxTyp Γ p)))
  --   → Σ↓ (μ-ctx Γ δ ε)
  --   → Σ↓ Γ

  -- transp-tree .(cns A (λ _ → nil)) A (lf-ctx .A) (cns↓ a nil↓) = a
  -- transp-tree .(μ-ctx Γ δ ε) A (nd-ctx Γ .A C δ ε) s =
  --   eqv-to C (lift-tree Γ δ ε s)

  -- -- μ-ctx : (Γ : Ctx) 
  -- --   → (δ : (p : CtxPos Γ) → Ctx)
  -- --   → (ε : (p : CtxPos Γ) → Tree (● (δ p) (CtxTyp Γ p)))
  -- --   → Ctx
  -- μ-ctx nil δ ε = nil
  -- μ-ctx (cns A B) δ ε = 
  --   let Γ' = δ (cns-here A B)
  --       a s = transp-tree Γ' A (ε (cns-here A B)) s
  --       δ' s t = δ (cns-there A B (a s) t)
  --       ε' s t = ε (cns-there A B (a s) t)
  --       ϕ s = μ-ctx (B (a s)) (δ' s) (ε' s)
  --   in γ-ctx Γ' ϕ

  -- lift-tree nil δ ε s = s
  -- lift-tree (cns A B) δ ε s = 
  --   let Γ' = δ (cns-here A B)
  --       a s = transp-tree Γ' A (ε (cns-here A B)) s
  --       δ' s t = δ (cns-there A B (a s) t)
  --       ε' s t = ε (cns-there A B (a s) t)
  --       ϕ s = μ-ctx (B (a s)) (δ' s) (ε' s)
  --       s' = γ-lift-fst Γ' ϕ s
  --   in cns↓ (a s') (lift-tree (B (a s')) (δ' s') (ε' s') (γ-lift-snd Γ' ϕ s))

  -- -- η : (f : Frm) (A : Cell f)
  -- --   → Tree f
  -- η (● Γ A) C =
  --   let η-ctx-dec p = η-ctx (CtxTyp Γ p)
  --       lf-ctx-dec p = lf-ctx (CtxTyp Γ p)
  --    in nd-ctx Γ A C η-ctx-dec lf-ctx-dec
  -- η (f ∥ σ ▸ τ) C = 
  --   let η-dec p = η (Typ σ p) (Inh σ p)
  --       lf-dec p = lf (Typ σ p) (Inh σ p)
  --   in nd f σ τ C η-dec lf-dec

  -- μ = {!!}
