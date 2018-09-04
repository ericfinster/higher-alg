{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util

-- 
-- We will try to use the following conventions for naming:
--
--  P, Q, R ... : Poly
--  i, j, k ... : I     (sorts ...)
--  f, g, h ... : Op    (operations ...)
--  p, q, r ... : Param (parameters ...)
--

module Polynomial where

  record Poly {ℓ} (I : Type ℓ) : Type (lsucc ℓ) where
    field
      Op : I → Type ℓ
      Param : {i : I} → Op i → I → Type ℓ

  open Poly public

  Ops : ∀ {ℓ} {I : Type ℓ} (P : Poly I) → Type ℓ
  Ops {I = I} P = Σ I (Op P)

  Arity : ∀ {ℓ} {I : Type ℓ} (P : Poly I)
    → {i : I} (f : Op P i) → Type ℓ
  Arity {I = I} P f = Σ I (Param P f)
  
  Decor : ∀ {ℓ} {I : Type ℓ} (P : Poly I)
    → {i : I} (f : Op P i) (X : I → Type ℓ)
    → Type ℓ
  Decor P f X = ∀ j → Param P f j → X j

  ⟦_⟧ : ∀ {ℓ} {I : Type ℓ} (P : Poly I) → (I → Type ℓ) → I → Type ℓ
  ⟦ P ⟧ X i = Σ (Op P i) (λ f → ∀ j → Param P f j → X j)

  module _ {ℓ} {I : Type ℓ} (P : Poly I) where

    data W : I → Type ℓ where
      lf : (i : I) → W i
      nd : {i : I} → ⟦ P ⟧ W i → W i

    Leaf : {i : I} (w : W i) → I → Type ℓ
    Leaf (lf i) j = i == j
    Leaf (nd (f , ϕ)) j = Σ I (λ k → Σ (Param P f k) (λ p → Leaf (ϕ k p) j))

    Node : {i : I} (w : W i) → Ops P → Type ℓ
    Node (lf i) p = Lift ⊥
    Node (nd {i} (f , ϕ)) jg = ((i , f) == jg) ⊔ Σ I (λ k → Σ (Param P f k) (λ p → Node (ϕ k p) jg))

    Frame : {i : I} (w : W i) (f : Op P i) → Type ℓ
    Frame w f = (j : I) → Leaf w j ≃ Param P f j

    Relator : Type (lsucc ℓ)
    Relator = {i : I} (w : W i) (f : Op P i) → Frame w f → Type ℓ

    corolla : {i : I} (f : Op P i) → W i
    corolla {i} f = nd (f , λ j p → lf j)

    corolla-lf-eqv : {i : I} (f : Op P i)
      → (j : I) → Leaf (corolla f) j ≃ Param P f j
    corolla-lf-eqv f j = equiv to from (λ _ → idp) from-to

      where to : Leaf (corolla f) j → Param P f j
            to (_ , p , idp) = p

            from : Param P f j → Leaf (corolla f) j
            from p = (j , p , idp) 

            from-to : (l : Leaf (corolla f) j) → from (to l) == l
            from-to (_ , p , idp) = idp

    -- These two invariance principles come up in a couple
    -- places, but I wonder if there isn't a more principled
    -- way to handle them ....
    
    lf-inv : {i j : I} (p : i == j) (w : W i)
      → ∀ k → Leaf w k ≃ Leaf (transport W p w) k
    lf-inv idp w k = ide (Leaf w k)

    nd-inv : {i j : I} (p : i == j) (w : W i)
      → (f : Ops P) → Node w f ≃ Node (transport W p w) f
    nd-inv idp w f = ide (Node w f)

    --
    --  Level calculations
    --
  
    W= : {i : I} → W i → W i → Type ℓ
    W= (lf i) (lf .i) = Lift ⊤
    W= (lf i) (nd _) = Lift ⊥
    W= (nd _) (lf i) = Lift ⊥
    W= (nd (f , ϕ)) (nd (g , ψ)) = Σ (f == g) decor-eq

      where decor-eq : f == g → Type ℓ
            decor-eq α = (k : I) (p : Param P f k) (q : Param P g k)
                         → (r : p == q [ (λ x → Param P x k) ↓ α ])
                         → ϕ k p == ψ k q 
    postulate

      W=-equiv : {i : I} (w₀ w₁ : W i) → (W= w₀ w₁) ≃ (w₀ == w₁)

    W-level-aux : ∀ {n} (op-lvl : (i : I) → has-level (S (S n)) (Op P i)) → (i : I) → has-level-aux (S (S n)) (W i)
    W-level-aux op-lvl i (lf .i) (lf .i) = equiv-preserves-level (W=-equiv (lf i) (lf i))
    W-level-aux op-lvl i (lf .i) (nd pw) = has-level-in (λ p → Empty-rec (lower (<– (W=-equiv (lf i) (nd pw)) p)))
    W-level-aux op-lvl i (nd pw) (lf .i) = has-level-in (λ p → Empty-rec (lower (<– (W=-equiv (nd pw) (lf i)) p)))
    W-level-aux op-lvl i (nd (f , ϕ)) (nd (g , ψ)) = equiv-preserves-level (W=-equiv (nd (f , ϕ)) (nd (g , ψ)))
      ⦃ Σ-level (has-level-apply (op-lvl i) f g) (λ α → Π-level (λ k → Π-level (λ p → Π-level (λ q →
                  Π-level (λ r → W-level-aux op-lvl k (ϕ k p) (ψ k q)))))) ⦄

    W-level : ∀ {n} (op-lvl : (i : I) → has-level (S (S n)) (Op P i)) → (i : I) → has-level (S (S n)) (W i)
    W-level op-lvl i = has-level-in (W-level-aux op-lvl i)

  --
  --  Need to rework level calculations using total spaces and arities ...
  --

  --   -- Leaf-level : ∀ {n} (s-lvl : has-level n I)
  --   --   → (p-lvl : {i : I} (f : Op P i) (j : I) → has-level n (Param P f j))
  --   --   → {i : I} (w : W i) (j : I)
  --   --   → has-level n (Leaf w j)
  --   -- Leaf-level s-lvl p-lvl (lf i) j = =-preserves-level s-lvl
  --   -- Leaf-level s-lvl p-lvl (nd (f , ϕ)) j = Σ-level s-lvl (λ k →
  --   --   Σ-level (p-lvl f k) (λ p → Leaf-level s-lvl p-lvl (ϕ k p) j))

  --   Leaf-level : ∀ {n} (s-lvl : has-level (S n) I)
  --     → (p-lvl : {i : I} (f : Op P i) → has-level n (Σ I (Param P f)))
  --     → {i : I} (w : W i) (j : I)
  --     → has-level n (Leaf w j)
  --   Leaf-level s-lvl p-lvl (lf i) j = has-level-apply s-lvl i j
  --   Leaf-level s-lvl p-lvl (nd (f , ϕ)) j = equiv-preserves-level Σ-assoc
  --     ⦃ Σ-level (p-lvl f) (λ { (i , p) → Leaf-level s-lvl p-lvl (ϕ i p) j }) ⦄
    
  --   -- Node-level : ∀ {n} (s-lvl : has-level (S (S n)) I)
  --   --   → (o-lvl : (i : I) → has-level (S (S n)) (Op P i))
  --   --   → (p-lvl : {i : I} (f : Op P i) (j : I) → has-level (S (S n)) (Param P f j))
  --   --   → {i : I} (w : W i) {j : I} (g : Op P j)
  --   --   → has-level (S (S n)) (Node w g)
  --   -- Node-level s-lvl o-lvl p-lvl (lf i) g = Lift-level Empty-level
  --   -- Node-level s-lvl o-lvl p-lvl (nd (f , ϕ)) g =
  --   --   Coprod-level (=-preserves-level (Σ-level s-lvl o-lvl))
  --   --                (Σ-level s-lvl (λ j → Σ-level (p-lvl f j)
  --   --                  (λ p → Node-level s-lvl o-lvl p-lvl (ϕ j p) g)))

  --   -- Is this maybe the more useful statement?  And similarly for leaves, by the way ...
  --   Node-level : ∀ {n} (s-lvl : has-level (S (S (S n))) I)
  --     → (o-lvl : (i : I) → has-level (S (S n)) (Op P i))
  --     → (p-lvl : {i : I} (f : Op P i) → has-level (S (S n)) (Σ I (Param P f)))
  --     → {i : I} (w : W i) {j : I} (g : Op P j)
  --     → has-level (S (S n)) (Node w g)
  --   Node-level s-lvl o-lvl p-lvl (lf i) g = Lift-level Empty-level
  --   Node-level s-lvl o-lvl p-lvl (nd (f , ϕ)) g =
  --     Coprod-level (has-level-apply (Σ-level s-lvl (λ j → raise-level _ (o-lvl j))) (_ , f) (_ , g))
  --                  (equiv-preserves-level Σ-assoc ⦃ Σ-level (p-lvl f) (λ { (j , p) → Node-level s-lvl o-lvl p-lvl (ϕ j p) g }) ⦄)

  --   -- Hmmm.  The natural implementation here uses the other, naive version
  --   -- Frame-level : ∀ {n} (s-lvl : has-level (S n) I)
  --   --   → (p-lvl : {i : I} (f : Op P i) → has-level n (Σ I (Param P f)))
  --   --   → {i : I} (w : W i) (f : Op P i)
  --   --   → has-level n (Frame w f)
  --   -- Frame-level s-lvl p-lvl w f = Π-level (λ i → ≃-level (Leaf-level s-lvl p-lvl w i) {!!})


  --
  --  Grafting of trees
  --
  
  module _ {ℓ} {I : Type ℓ} (P : Poly I) where

    graft : {i : I} (w : W P i) (ψ : ∀ j → Leaf P w j → W P j) → W P i
    graft (lf i) ψ = ψ i idp
    graft (nd (f , ϕ)) ψ = nd (f , λ j p → graft (ϕ j p) (λ k l → ψ k (j , p , l)))

    --
    --  Leaves in a graft
    --

    graft-leaf-in : {i : I} (w : W P i) (ψ : ∀ j → Leaf P w j → W P j)
      → (j : I) (k : I) (l : Leaf P w k) (m : Leaf P (ψ k l) j)
      → Leaf P (graft w ψ) j
    graft-leaf-in (lf i) ψ j .i idp m = m
    graft-leaf-in (nd (f , ϕ)) ψ j k (h , p , l) m =
      h , p , graft-leaf-in (ϕ h p) (λ k₁ l₁ → ψ k₁ (h , p , l₁)) j k l m
      
    graft-leaf-elim : ∀ {ℓ'} {i : I} (w : W P i) (ψ : ∀ j → Leaf P w j → W P j) 
      → (j : I) (Q : (l : Leaf P (graft w ψ) j) → Type ℓ')
      → (σ : (k : I) (l : Leaf P w k) (m : Leaf P (ψ k l) j)
             → Q (graft-leaf-in w ψ j k l m))
      → (l : Leaf P (graft w ψ) j) → Q l
    graft-leaf-elim (lf i) ψ j Q σ l = σ i idp l
    graft-leaf-elim (nd (f , ϕ)) ψ j Q σ (h , p , l) = 
      graft-leaf-elim (ϕ h p) (λ j₁ l₁ → ψ j₁ (h , p , l₁)) j
        (λ l₁ → Q (h , p , l₁)) (λ k₁ l₁ m₁ → σ k₁ (h , p , l₁) m₁) l

    graft-leaf-elim-β : ∀ {ℓ'} {i : I} (w : W P i) (ψ : ∀ j → Leaf P w j → W P j) 
      → (j : I) (Q : (l : Leaf P (graft w ψ) j) → Type ℓ')
      → (σ : (k : I) (l : Leaf P w k) (m : Leaf P (ψ k l) j)
             → Q (graft-leaf-in w ψ j k l m))
      → (k : I) (l : Leaf P w k) (m : Leaf P (ψ k l) j)
      → graft-leaf-elim w ψ j Q σ (graft-leaf-in w ψ j k l m) == σ k l m
    graft-leaf-elim-β (lf i) ψ j Q σ .i idp m = idp
    graft-leaf-elim-β (nd (f , ϕ)) ψ j Q σ k (h , p , l) m =
      graft-leaf-elim-β (ϕ h p) (λ j₁ l₁ → ψ j₁ (h , p , l₁)) j
        (λ l₁ → Q (h , p , l₁)) (λ k₁ l₁ m₁ → σ k₁ (h , p , l₁) m₁) k l m

    graft-leaf-rec : ∀ {ℓ'} {A : Type ℓ'}
      → {i : I} (w : W P i) (ψ : ∀ j → Leaf P w j → W P j)
      → (j : I) (σ : (k : I) (l : Leaf P w k) (m : Leaf P (ψ k l) j) → A)
      → (l : Leaf P (graft w ψ) j) → A
    graft-leaf-rec {A = A} w ψ j σ = graft-leaf-elim w ψ j (cst A) σ

    graft-leaf-rec-β : ∀ {ℓ'} {A : Type ℓ'}
      → {i : I} (w : W P i) (ψ : ∀ j → Leaf P w j → W P j)
      → (j : I) (σ : (k : I) (l : Leaf P w k) (m : Leaf P (ψ k l) j) → A)
      → (k : I) (l : Leaf P w k) (m : Leaf P (ψ k l) j)
      → graft-leaf-rec w ψ j σ (graft-leaf-in w ψ j k l m) == σ k l m
    graft-leaf-rec-β {A = A} w ψ j σ = graft-leaf-elim-β w ψ j (cst A) σ

    module _ {i : I} (w : W P i) (ψ : ∀ j → Leaf P w j → W P j) (j : I) where

      graft-leaf-to : Σ I (λ k → Σ (Leaf P w k) (λ l → Leaf P (ψ k l) j)) → Leaf P (graft w ψ) j
      graft-leaf-to (k , l , m) = graft-leaf-in w ψ j k l m

      graft-leaf-from : Leaf P (graft w ψ) j → Σ I (λ k → Σ (Leaf P w k) (λ l → Leaf P (ψ k l) j))
      graft-leaf-from = graft-leaf-rec w ψ j (λ k l m → k , l , m) 

      abstract
      
        graft-leaf-to-from : (l : Leaf P (graft w ψ) j)
          → graft-leaf-to (graft-leaf-from l) == l
        graft-leaf-to-from = graft-leaf-elim w ψ j (λ l → graft-leaf-to (graft-leaf-from l) == l) 
          (λ k l m → ap (graft-leaf-to) (graft-leaf-rec-β w ψ j (λ k l m → k , l , m) k l m))

        graft-leaf-from-to : (l : Σ I (λ k → Σ (Leaf P w k) (λ l → Leaf P (ψ k l) j)))
          → graft-leaf-from (graft-leaf-to l) == l
        graft-leaf-from-to (k , l , m) = graft-leaf-rec-β w ψ j (λ k l m → k , l , m) k l m

      graft-leaf-eqv : Σ I (λ k → Σ (Leaf P w k) (λ l → Leaf P (ψ k l) j)) ≃ Leaf P (graft w ψ) j
      graft-leaf-eqv = equiv graft-leaf-to graft-leaf-from
                             graft-leaf-to-from graft-leaf-from-to
                                   
    --
    --  Nodes in a graft
    --
    
    graft-node-inl : {i : I} (w : W P i) (ψ : ∀ j → Leaf P w j → W P j) (g : Ops P)
      → Node P w g → Node P (graft w ψ) g
    graft-node-inl (lf i) ψ g (lift ())
    graft-node-inl (nd (f , ϕ)) ψ ._ (inl idp) = inl idp
    graft-node-inl (nd (f , ϕ)) ψ g (inr (h , p , n)) =
      inr (h , p , graft-node-inl (ϕ h p) (λ k l → ψ k (h , p , l)) g n)

    graft-node-inr : {i : I} (w : W P i) (ψ : ∀ j → Leaf P w j → W P j) (g : Ops P)
      → (k : I) (l : Leaf P w k) (n : Node P (ψ k l) g)
      → Node P (graft w ψ) g
    graft-node-inr (lf i) ψ g .i idp n = n
    graft-node-inr (nd (f , ϕ)) ψ g k (h , p , l) n =
      inr (h , p , graft-node-inr (ϕ h p) (λ k l → ψ k (h , p , l)) g k l n)

    graft-node-elim : ∀ {ℓ'} {i : I} (w : W P i) (ψ : ∀ j → Leaf P w j → W P j)
      → (g : Ops P) (Q : Node P (graft w ψ) g → Type ℓ')
      → (inl* : (n : Node P w g) → Q (graft-node-inl w ψ g n))
      → (inr* : (k : I) (l : Leaf P w k) (n : Node P (ψ k l) g)
              →  Q (graft-node-inr w ψ g k l n))
      → (n : Node P (graft w ψ) g) → Q n
    graft-node-elim (lf i) ψ g Q inl* inr* n = inr* i idp n
    graft-node-elim (nd (f , ϕ)) ψ .(_ , f) Q inl* inr* (inl idp) = inl* (inl idp)
    graft-node-elim (nd (f , ϕ)) ψ g Q inl* inr* (inr (h , p , n)) = 
      graft-node-elim (ϕ h p) (λ k l → ψ k (h , p , l)) g
        (λ n₁ → Q (inr (h , p , n₁))) (λ n₁ → inl* (inr (h , p , n₁)))
        (λ k l n₁ → inr* k (h , p , l) n₁) n

    graft-node-elim-inl-β : ∀ {ℓ'} {i : I} (w : W P i) (ψ : ∀ j → Leaf P w j → W P j)
      → (g : Ops P) (Q : Node P (graft w ψ) g → Type ℓ')
      → (inl* : (n : Node P w g) → Q (graft-node-inl w ψ g n))
      → (inr* : (k : I) (l : Leaf P w k) (n : Node P (ψ k l) g)
              →  Q (graft-node-inr w ψ g k l n))
      → (n : Node P w g)
      → graft-node-elim w ψ g Q inl* inr* (graft-node-inl w ψ g n) == inl* n
    graft-node-elim-inl-β (lf i) ψ g Q inl* inr* (lift ())
    graft-node-elim-inl-β (nd (f , ϕ)) ψ .(_ , f) Q inl* inr* (inl idp) = idp
    graft-node-elim-inl-β (nd (f , ϕ)) ψ g Q inl* inr* (inr (h , p , n)) =
      graft-node-elim-inl-β (ϕ h p) (λ k l → ψ k (h , p , l)) g
        (λ n₁ → Q (inr (h , p , n₁))) (λ n₁ → inl* (inr (h , p , n₁)))
        (λ k l n₁ → inr* k (h , p , l) n₁) n

    graft-node-elim-inr-β : ∀ {ℓ'} {i : I} (w : W P i) (ψ : ∀ j → Leaf P w j → W P j)
      → (g : Ops P) (Q : Node P (graft w ψ) g → Type ℓ')
      → (inl* : (n : Node P w g) → Q (graft-node-inl w ψ g n))
      → (inr* : (k : I) (l : Leaf P w k) (n : Node P (ψ k l) g)
              →  Q (graft-node-inr w ψ g k l n))
      → (k : I) (l : Leaf P w k) (n : Node P (ψ k l) g)
      → graft-node-elim w ψ g Q inl* inr* (graft-node-inr w ψ g k l n) == inr* k l n
    graft-node-elim-inr-β (lf i) ψ g Q inl* inr* .i idp n = idp
    graft-node-elim-inr-β (nd (f , ϕ)) ψ g Q inl* inr* k (h , p , l) n =
      graft-node-elim-inr-β (ϕ h p) (λ k l → ψ k (h , p , l)) g
        (λ n₁ → Q (inr (h , p , n₁))) (λ n₁ → inl* (inr (h , p , n₁)))
        (λ k l n₁ → inr* k (h , p , l) n₁) k l n

    graft-node-rec : ∀ {ℓ'} {A : Type ℓ'}
      → {i : I} (w : W P i) (ψ : ∀ j → Leaf P w j → W P j) (g : Ops P)
      → (inl* : (n : Node P w g) → A)
      → (inr* : (k : I) (l : Leaf P w k) (n : Node P (ψ k l) g) → A)
      → (n : Node P (graft w ψ) g) → A
    graft-node-rec {A = A} w ψ g inl* inr* =
      graft-node-elim w ψ g (cst A) inl* inr*  

    graft-node-rec-inl-β : ∀ {ℓ'} {A : Type ℓ'}
      → {i : I} (w : W P i) (ψ : ∀ j → Leaf P w j → W P j) (g : Ops P)
      → (inl* : (n : Node P w g) → A)
      → (inr* : (k : I) (l : Leaf P w k) (n : Node P (ψ k l) g) → A)
      → (n : Node P w g)
      → graft-node-rec w ψ g inl* inr* (graft-node-inl w ψ g n) == inl* n
    graft-node-rec-inl-β {A = A} w ψ g inl* inr* =
      graft-node-elim-inl-β w ψ g (cst A) inl* inr*

    graft-node-rec-inr-β : ∀ {ℓ'} {A : Type ℓ'}
      → {i : I} (w : W P i) (ψ : ∀ j → Leaf P w j → W P j) (g : Ops P)
      → (inl* : (n : Node P w g) → A)
      → (inr* : (k : I) (l : Leaf P w k) (n : Node P (ψ k l) g) → A)
      → (k : I) (l : Leaf P w k) (n : Node P (ψ k l) g)
      → graft-node-rec w ψ g inl* inr* (graft-node-inr w ψ g k l n) == inr* k l n
    graft-node-rec-inr-β {A = A} w ψ g inl* inr* = 
      graft-node-elim-inr-β w ψ g (cst A) inl* inr*

    module _ {i : I} (w : W P i) (ψ : ∀ j → Leaf P w j → W P j) (g : Ops P) where

      graft-node-to : Node P w g ⊔ Σ I (λ k → Σ (Leaf P w k) (λ l → Node P (ψ k l) g)) → Node P (graft w ψ) g
      graft-node-to (inl n) = graft-node-inl w ψ g n
      graft-node-to (inr (k , l , n)) = graft-node-inr w ψ g k l n
      
      graft-node-from : Node P (graft w ψ) g → Node P w g ⊔ Σ I (λ k → Σ (Leaf P w k) (λ l → Node P (ψ k l) g))
      graft-node-from = graft-node-rec w ψ g inl (λ k l n → inr (k , l , n))

      abstract
      
        graft-node-to-from : (n : Node P (graft w ψ) g)
          → graft-node-to (graft-node-from n) == n
        graft-node-to-from = graft-node-elim w ψ g (λ n → graft-node-to (graft-node-from n) == n)
          (λ n → ap graft-node-to (graft-node-rec-inl-β w ψ g inl (λ k l n → inr (k , l , n)) n))
          (λ k l n → ap graft-node-to (graft-node-rec-inr-β w ψ g inl (λ k l n → inr (k , l , n)) k l n))

        graft-node-from-to : (n : Node P w g ⊔ Σ I (λ k → Σ (Leaf P w k) (λ l → Node P (ψ k l) g)))
          → graft-node-from (graft-node-to n) == n
        graft-node-from-to (inl n) = graft-node-rec-inl-β w ψ g inl (λ k l n → inr (k , l , n)) n
        graft-node-from-to (inr (k , l , n)) = graft-node-rec-inr-β w ψ g inl (λ k l n → inr (k , l , n)) k l n
      
      graft-node-eqv : Node P w g ⊔ Σ I (λ k → Σ (Leaf P w k) (λ l → Node P (ψ k l) g)) ≃ Node P (graft w ψ) g
      graft-node-eqv = equiv graft-node-to graft-node-from 
                             graft-node-to-from graft-node-from-to 

    --
    -- Basic laws of grafting
    --

    -- grafting is unital
    graft-unit : {i : I} (w : W P i) → graft w (λ j l → lf j) == w
    graft-unit (lf i) = idp
    graft-unit (nd (f , ϕ)) =
      ap (λ x → nd (f , x)) (λ= (λ j → λ= (λ l → graft-unit (ϕ j l))))

    -- grafting is associative
    graft-assoc : {i : I} (w : W P i)
      → (ψ₀ : ∀ j → Leaf P w j → W P j)
      → (ψ₁ : ∀ j k → (l : Leaf P w k) → Leaf P (ψ₀ k l) j → W P j)
      → graft (graft w ψ₀) (λ j → graft-leaf-rec w ψ₀ j (ψ₁ j))
        == graft w (λ j l → graft (ψ₀ j l) (λ k m → ψ₁ k j l m))
    graft-assoc (lf i) ψ₀ ψ₁ = idp
    graft-assoc (nd (f , ϕ)) ψ₀ ψ₁ = ap (λ x → nd (f , x))
      (λ= (λ h → λ= (λ p → graft-assoc (ϕ h p) (λ k l → ψ₀ k (h , p , l))
        (λ j k l m → ψ₁ j k (h , p , l) m))))

  --
  --  Domains and slicing
  --

  -- The "slice" of a polynomial by a relator
  _//_ : ∀ {ℓ} {I : Type ℓ} (P : Poly I) (R : Relator P) → Poly (Σ I (Op P))
  Op (P // R) (i , f) = Σ (W P i) (λ w → Σ (Frame P w f) (R w f))
  Param (P // R) (w , α , r) g = Node P w g
  
  record Domain {ℓ} {I : Type ℓ} (P : Poly I) : Type (lsucc ℓ) where
    coinductive
    field

      Rl : Relator P 
      Dm : Domain (P // Rl)

  open Domain public
