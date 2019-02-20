{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial

module Grafting {ℓ} {I : Type ℓ} (P : Poly I) where

  graft : {i : I} (w : W P i) (ψ : ∀ j → Leaf P w j → W P j) → W P i
  graft (lf i) ψ = ψ i idp
  graft (nd (f ,  ϕ)) ψ = 
    let ψ' j p k l = ψ k (j , p , l)
        ϕ' j p = graft (ϕ j p) (ψ' j p)
    in nd (f ,  ϕ')

  --
  --  Leaves in a graft
  --

  graft-leaf-to : {i : I} (w : W P i) (ψ : ∀ j → Leaf P w j → W P j) (k : I)
    → Σ I (λ j → Σ (Leaf P w j) (λ l → Leaf P (ψ j l) k))
    → Leaf P (graft w ψ) k
  graft-leaf-to (lf i) ψ k (.i , idp , l) = l
  graft-leaf-to (nd (f ,  ϕ)) ψ k (j₁ , (j₀ , p , l₀) , l₁) = 
    let ψ' j p k l = ψ k (j , p , l)
    in (j₀ , p , graft-leaf-to (ϕ j₀ p) (ψ' j₀ p) k (j₁ , l₀ , l₁))

  graft-leaf-from : {i : I} (w : W P i) (ψ : ∀ j → Leaf P w j → W P j) (k : I)
    → Leaf P (graft w ψ) k
    → Σ I (λ j → Σ (Leaf P w j) (λ l → Leaf P (ψ j l) k))
  graft-leaf-from (lf i) ψ k l = i , idp , l
  graft-leaf-from (nd (f ,  ϕ)) ψ k (j , p , l) = 
    let (s , t , u) = graft-leaf-from (ϕ j p) (λ k l → ψ k (j , p , l)) k l
    in s , (j , p , t) , u

  graft-leaf-to-from : {i : I} (w : W P i) (ψ : ∀ j → Leaf P w j → W P j)
    → (k : I) (l : Leaf P (graft w ψ) k)
    → graft-leaf-to w ψ k (graft-leaf-from w ψ k l) == l
  graft-leaf-to-from (lf i) ψ k l = idp
  graft-leaf-to-from (nd (f ,  ϕ)) ψ k (j , p , l) =
    let ψ' j p k l = ψ k (j , p , l)
    in ap (λ x → (j , p , x)) (graft-leaf-to-from (ϕ j p) (ψ' j p) k l) 

  graft-leaf-from-to : {i : I} (w : W P i) (ψ : ∀ j → Leaf P w j → W P j) (k : I)
    → (l : Σ I (λ j → Σ (Leaf P w j) (λ l → Leaf P (ψ j l) k)))
    → graft-leaf-from w ψ k (graft-leaf-to w ψ k l) == l
  graft-leaf-from-to (lf i) ψ k (.i , idp , l₁) = idp
  graft-leaf-from-to (nd (f ,  ϕ)) ψ k (j₁ , (j₀ , p , l₀) , l₁) =
    let ψ' j p k l = ψ k (j , p , l)
        ih = graft-leaf-from-to (ϕ j₀ p) (ψ' j₀ p) k (j₁ , l₀ , l₁)
    in ap (λ x → (fst x , (j₀ , p , fst (snd x)) , snd (snd x))) ih

  graft-leaf-eqv : {i : I} (w : W P i) (ψ : ∀ j → Leaf P w j → W P j) (k : I)
    → Σ I (λ j → Σ (Leaf P w j) (λ l → Leaf P (ψ j l) k)) ≃ Leaf P (graft w ψ) k
  graft-leaf-eqv w ψ k =
    equiv (graft-leaf-to w ψ k) (graft-leaf-from w ψ k)
          (graft-leaf-to-from w ψ k) (graft-leaf-from-to w ψ k)

  -- graft-lf-elim : ∀ {ℓ'} {i : I} {w : W P i}
  --   → {ψ : ∀ j → Leaf P w j → W P j} {j : I}
  --   → (Q : (l : Leaf P (graft w ψ) j) → Type ℓ')
  --   → (f : (k : I) (l₀ : Leaf P w k) (l₁ : Leaf P (ψ k l₀) j)
  --        → Q (graft-leaf-to w ψ j (k , l₀ , l₁) ))
  --   → (l : Leaf P (graft w ψ) j) → Q l
  -- graft-lf-elim {w = w} {ψ = ψ} {j = j} Q f l =
  --   let (k , l₀ , l₁) = graft-leaf-from w ψ j l
  --   in transport Q (graft-leaf-to-from w ψ j l) (f k l₀ l₁)

  -- postulate

  --   graft-lf-elim-unfold : ∀ {ℓ'} {i : I} {f : Op P i}
  --     → {ϕ : ∀ j → Param P f j → W P j}
  --     → {ψ : ∀ j → Leaf P (nd (f , ϕ)) j → W P j} {j : I}
  --     → (Q : (l : Leaf P (graft (nd (f , ϕ)) ψ) j) → Type ℓ')
  --     → (σ : (k : I) (l₀ : Leaf P (nd (f , ϕ)) k) (l₁ : Leaf P (ψ k l₀) j)
  --          → Q (graft-leaf-to (nd (f , ϕ)) ψ j (k , l₀ , l₁) ))
  --     → (k : I) (p : Param P f k) (l : Leaf P (graft (ϕ k p) (λ k' l → ψ k' (k , p , l))) j)
  --     → graft-lf-elim {w = ϕ k p} (λ l₀ → Q (k , p , l₀)) (λ k' l₀ l₁ → σ k' (k , p , l₀) l₁) l
  --       == graft-lf-elim Q σ (k , p , l)

  -- abstract

  --   graft-lf-rec : ∀ {ℓ'} {A : Type ℓ'} {i : I} {w : W P i}
  --     → {ψ : ∀ j → Leaf P w j → W P j} {k : I}
  --     → (f : Σ I (λ j → Σ (Leaf P w j) (λ l → Leaf P (ψ j l) k)) → A)
  --     → Leaf P (graft w ψ) k → A
  --   graft-lf-rec {w = w} {ψ = ψ} {k = k} f l =
  --     f (graft-leaf-from w ψ k l)

  -- Implicit versions
  graft-lf-to : {i : I} {w : W P i}
    → {ψ : ∀ j → Leaf P w j → W P j} {k : I}
    → Σ I (λ j → Σ (Leaf P w j) (λ l → Leaf P (ψ j l) k))
    → Leaf P (graft w ψ) k
  graft-lf-to {i} {w} {ψ} {k} = graft-leaf-to w ψ k
  
  graft-lf-from : {i : I} {w : W P i}
    → {ψ : ∀ j → Leaf P w j → W P j} {k : I}
    → Leaf P (graft w ψ) k
    → Σ I (λ j → Σ (Leaf P w j) (λ l → Leaf P (ψ j l) k))
  graft-lf-from {i} {w} {ψ} {k} = graft-leaf-from w ψ k

  --
  --  Nodes in a graft
  --

  graft-node-to : {i : I} (w : W P i)
    → (ψ : ∀ j → Leaf P w j → W P j) (g : Ops P)
    → Node P w g ⊔ Σ I (λ k → Σ (Leaf P w k) (λ l → Node P (ψ k l) g))
    → Node P (graft w ψ) g
  graft-node-to (lf i) ψ g (inl ())
  graft-node-to (lf i) ψ g (inr (.i , idp , n)) = n
  graft-node-to (nd (f ,  ϕ)) ψ ._ (inl (inl idp)) = inl idp
  graft-node-to (nd (f ,  ϕ)) ψ g (inl (inr (j , p , n))) =
    inr (j , p , graft-node-to (ϕ j p) (λ k l → ψ k (j , p , l)) g (inl n))
  graft-node-to (nd (f ,  ϕ)) ψ g (inr (k , (j , p , l) , n)) = 
    inr (j , p , graft-node-to (ϕ j p) (λ k l → ψ k (j , p , l)) g (inr (k , l , n)))

  graft-node-from : {i : I} (w : W P i)
    → (ψ : ∀ j → Leaf P w j → W P j) (g : Ops P)
    → Node P (graft w ψ) g
    → Node P w g ⊔ Σ I (λ k → Σ (Leaf P w k) (λ l → Node P (ψ k l) g))

  graft-node-from-lcl : {i : I} (f : Op P i)
    → (ϕ : ∀ j → Param P f j → W P j)
    → (ψ : ∀ j → Leaf P (nd (f , ϕ)) j → W P j)
    → (g : Ops P) (j : I) (p : Param P f j)
    → (n : Node P (ϕ j p) g ⊔ Σ I (λ k → Σ (Leaf P (ϕ j p) k) (λ l → Node P (ψ k (j , p , l)) g)))
    → Node P (nd (f , ϕ)) g ⊔ Σ I (λ k → Σ (Leaf P (nd (f , ϕ)) k) (λ l → Node P (ψ k l) g))

  graft-node-from (lf i) ψ g n = inr (i , idp , n)
  graft-node-from (nd (f ,  ϕ)) ψ ._ (inl idp) = inl (inl idp)
  graft-node-from (nd (f ,  ϕ)) ψ g (inr (j , p , n)) =
    graft-node-from-lcl f ϕ ψ g j p
      (graft-node-from (ϕ j p) (λ k l → ψ k (j , p , l)) g n)

  graft-node-from-lcl f ϕ ψ g j p =
    ⊔-rec (λ n → inl (inr (j , p , n)))
          (λ t → let (k , l , n) = t in inr ((k , (j , p , l) , n)))

  abstract

    graft-node-to-from : {i : I} (w : W P i)
      → (ψ : ∀ j → Leaf P w j → W P j) (g : Ops P)
      → (n : Node P (graft w ψ) g)
      → graft-node-to w ψ g (graft-node-from w ψ g n) == n

    graft-node-to-from-lcl : {i : I} (f : Op P i)
      → (ϕ : ∀ j → Param P f j → W P j)
      → (ψ : ∀ j → Leaf P (nd (f , ϕ)) j → W P j)
      → (g : Ops P) (j : I) (p : Param P f j)
      → (n : Node P (ϕ j p) g ⊔ Σ I (λ k → Σ (Leaf P (ϕ j p) k) (λ l → Node P (ψ k (j , p , l)) g)))
      → graft-node-to (nd (f , ϕ)) ψ g (graft-node-from-lcl f ϕ ψ g j p n)
        == inr (j , p , graft-node-to (ϕ j p) (λ k l → ψ k (j , p , l)) g n)

    graft-node-to-from (lf i) ψ g n = idp
    graft-node-to-from (nd (f ,  ϕ)) ψ ._ (inl idp) = idp
    graft-node-to-from (nd (f ,  ϕ)) ψ g (inr (j , p , n)) =
      graft-node-to-from-lcl f ϕ ψ g j p
        (graft-node-from (ϕ j p) (λ k l → ψ k (j , p , l)) g n) ∙
      ap (λ x → inr (j , p , x)) (graft-node-to-from (ϕ j p) (λ k l → ψ k (j , p , l)) g n)

    graft-node-to-from-lcl f ϕ ψ g j p (inl n) = idp
    graft-node-to-from-lcl f ϕ ψ g j p (inr (k , l , n)) = idp

    graft-node-from-to : {i : I} (w : W P i)
      → (ψ : ∀ j → Leaf P w j → W P j) (g : Ops P)
      → (n : Node P w g ⊔ Σ I (λ k → Σ (Leaf P w k) (λ l → Node P (ψ k l) g)))
      → graft-node-from w ψ g (graft-node-to w ψ g n) == n
    graft-node-from-to (lf i) ψ g (inl ())
    graft-node-from-to (lf i) ψ g (inr (.i , idp , n)) = idp
    graft-node-from-to (nd (f ,  ϕ)) ψ ._ (inl (inl idp)) = idp
    graft-node-from-to (nd (f ,  ϕ)) ψ g (inl (inr (j , p , n))) = 
      ap (graft-node-from-lcl f ϕ ψ g j p)
         (graft-node-from-to (ϕ j p) (λ k l → ψ k (j , p , l)) g (inl n))
    graft-node-from-to (nd (f ,  ϕ)) ψ g (inr (k , (j , p , l) , n)) =
      ap (graft-node-from-lcl f ϕ ψ g j p)
         (graft-node-from-to (ϕ j p) (λ k l → ψ k (j , p , l)) g (inr (k , l , n)))

  graft-node-eqv : {i : I} (w : W P i)
    → (ψ : ∀ j → Leaf P w j → W P j)
    → (g : Ops P)
    → Node P w g ⊔ Σ I (λ k → Σ (Leaf P w k) (λ l → Node P (ψ k l) g))
      ≃ Node P (graft w ψ) g
  graft-node-eqv w ψ g =
    equiv (graft-node-to w ψ g) (graft-node-from w ψ g)
          (graft-node-to-from w ψ g) (graft-node-from-to w ψ g)


  --
  --  An elimination priciple for nodes
  -- 

  -- graft-nd-inl : {i : I} {w : W P i}
  --   → {ψ : ∀ j → Leaf P w j → W P j} {g : Ops P}
  --   → Node P w g → Node P (graft w ψ) g
  -- graft-nd-inl {w = w} {ψ = ψ} {g = g} n =
  --   graft-node-to w ψ g (inl n)

  -- graft-nd-inr : {i : I} {w : W P i}
  --   → {ψ : ∀ j → Leaf P w j → W P j} {g : Ops P}
  --   → Σ I (λ k → Σ (Leaf P w k) (λ l → Node P (ψ k l) g))
  --   → Node P (graft w ψ) g
  -- graft-nd-inr {w = w} {ψ = ψ} {g = g} t =
  --   graft-node-to w ψ g (inr t)

  -- graft-node-elim : ∀ {ℓ'} {i : I} {w : W P i}
  --   → {ψ : ∀ j → Leaf P w j → W P j} {g : Ops P}
  --   → (Q : (n : Node P (graft w ψ) g) → Type ℓ')
  --   → (inl* : (n : Node P w g) → Q (graft-nd-inl n))
  --   → (inr* : (j : I) (l : Leaf P w j) (n : Node P (ψ j l) g) → Q (graft-nd-inr (j , l , n)))
  --   → (n : Node P (graft w ψ) g) → Q n
  -- graft-node-elim {ℓ'} {w = w} {ψ = ψ} {g = g} Q inl* inr* n =
  --   transport Q (<–-inv-r (graft-node-eqv w ψ g) n)
  --               (⊔-elim {C = λ x → Q (graft-node-to w ψ g x)} inl* (λ { (j , l , n) → inr* j l n })
  --                       (graft-node-from w ψ g n))

  -- -- A recursor helps to organize structurally recursive
  -- -- definitions on nodes.
  -- graft-node-rec : ∀ {ℓ'} {A : Type ℓ'} 
  --   → {i : I} {w : W P i} {ψ : ∀ j → Leaf P w j → W P j} {g : Ops P}
  --   → (inl* : (n : Node P w g) → A)
  --   → (inr* : (j : I) (l : Leaf P w j) → Node P (ψ j l) g → A)
  --   → Node P (graft w ψ) g → A
  -- graft-node-rec {w = w} {ψ = ψ} {g = g} inl* inr* n =
  --   ⊔-rec inl* (λ { (j , l , n) → inr* j l n  }) (graft-node-from w ψ g n)

  -- postulate

  --   graft-node-rec-unfold : ∀ {ℓ'} {A : Type ℓ'}
  --     → {i : I} {f : Op P i} {ϕ : ∀ j → Param P f j → W P j}
  --     → {ψ : ∀ j → Leaf P (nd (f , ϕ)) j → W P j} {g : Ops P}
  --     → (inl* : (n : Node P (nd (f , ϕ)) g) → A)
  --     → (inr* : (j : I) (l : Leaf P (nd (f , ϕ)) j) → Node P (ψ j l) g → A)
  --     → (j : I) (p : Param P f j) (n : Node P (graft (ϕ j p) (λ k l → ψ k (j , p , l))) g)
  --     → graft-node-rec {w = ϕ j p} (λ n₀ → inl* (inr (j , p , n₀)))
  --                                  (λ k l n₀ → inr* k (j , p , l) n₀) n
  --       == graft-node-rec {w = nd (f , ϕ)} inl* inr* (inr (j , p , n))             
  --   --graft-node-rec-unfold = {!!}

  --   graft-node-rec-inl-β : ∀ {ℓ'} {A : Type ℓ'} 
  --     → {i : I} {w : W P i} {ψ : ∀ j → Leaf P w j → W P j} {g : Ops P}
  --     → (inl* : (n : Node P w g) → A)
  --     → (inr* : (j : I) (l : Leaf P w j) → Node P (ψ j l) g → A)
  --     → (n : Node P w g)
  --     → graft-node-rec inl* inr* (graft-nd-inl n) == inl* n
  --   -- graft-node-rec-inl-β {w = w} {ψ = ψ} {g = g} inl* inr* n =
  --   --   {!!}

  --   graft-node-rec-inr-β : ∀ {ℓ'} {A : Type ℓ'} 
  --     → {i : I} {w : W P i} {ψ : ∀ j → Leaf P w j → W P j} {g : Ops P}
  --     → (inl* : (n : Node P w g) → A)
  --     → (inr* : (j : I) (l : Leaf P w j) → Node P (ψ j l) g → A)
  --     → (j : I) (l : Leaf P w j) (n : Node P (ψ j l) g)
  --     → graft-node-rec inl* inr* (graft-nd-inr (j , l , n)) == inr* j l n
  --   -- graft-node-rec-inr-β {w = w} {ψ = ψ} {g = g} inl* inr* j l n =
  --   --   {!!}

  graft-nd-to : {i : I} {w : W P i}
    → {ψ : ∀ j → Leaf P w j → W P j} {g : Ops P}
    → Node P w g ⊔ Σ I (λ k → Σ (Leaf P w k) (λ l → Node P (ψ k l) g))
    → Node P (graft w ψ) g
  graft-nd-to {i} {w} {ψ} {g} =
    graft-node-to w ψ g

  graft-nd-from : {i : I} {w : W P i}
    → {ψ : ∀ j → Leaf P w j → W P j} {g : Ops P}
    → Node P (graft w ψ) g
    → Node P w g ⊔ Σ I (λ k → Σ (Leaf P w k) (λ l → Node P (ψ k l) g))
  graft-nd-from {i} {w} {ψ} {g} =
    graft-node-from w ψ g

  graft-nd-to-from : {i : I} {w : W P i}
    → {ψ : ∀ j → Leaf P w j → W P j} {g : Ops P}
    → (n : Node P (graft w ψ) g)
    → graft-node-to w ψ g (graft-node-from w ψ g n) == n
  graft-nd-to-from {i} {w} {ψ} {g} =
    graft-node-to-from w ψ g
  
  graft-nd-from-to : {i : I} {w : W P i}
    → {ψ : ∀ j → Leaf P w j → W P j} {g : Ops P}
    → (n : Node P w g ⊔ Σ I (λ k → Σ (Leaf P w k) (λ l → Node P (ψ k l) g)))
    → graft-node-from w ψ g (graft-node-to w ψ g n) == n
  graft-nd-from-to {i} {w} {ψ} {g} =
    graft-node-from-to w ψ g


  -- The polynomial underlying the free monad
  Fr : Poly I
  Op Fr = W P
  Param Fr = Leaf P

  -- Some useful path-over principles....
  ↓-graft-Leaf-ih₀ : {i j : I} {w : W P i}
    → {ψ₀ ψ₁ : Decor Fr w (W P)} (e : ψ₀ == ψ₁)
    → (k : I) (l : Leaf P w k)
    → {l₀ : Leaf P (ψ₀ k l) j} {l₁ : Leaf P (ψ₁ k l) j}
    → l₀ == l₁ [ (λ x → Leaf P x j) ↓ app= (app= e k) l ]
    → graft-lf-to (k , l , l₀) == graft-lf-to (k , l , l₁) [ (λ x → Leaf P (graft w x) j) ↓ e ]
  ↓-graft-Leaf-ih₀ idp k p idp = idp

  ↓-graft-Leaf-ih : {i j : I} {w : W P i}
    → {ψ₀ ψ₁ : Decor Fr w (W P)} 
    → (H : (k : I) (l : Leaf P w k) → ψ₀ k l == ψ₁ k l)
    → (k : I) (l : Leaf P w k)
    → {l₀ : Leaf P (ψ₀ k l) j} {l₁ : Leaf P (ψ₁ k l) j}
    → l₀ == l₁ [ (λ x → Leaf P x j) ↓ H k l ]
    → graft-lf-to (k , l , l₀) == graft-lf-to (k , l , l₁) [ (λ x → Leaf P (graft w x) j) ↓ Decor-== Fr H ]
  ↓-graft-Leaf-ih H k l {l₀} {l₁} q =
    ↓-graft-Leaf-ih₀ (Decor-== Fr H) k l
      (transport (λ y → l₀ == l₁ [ (λ x → Leaf P x _) ↓ y ])
                 (Decor-==-β Fr H k l) q)

  --
  -- Basic laws of grafting
  --

  -- grafting is unital
  graft-unit : {i : I} (w : W P i) → w == graft w (λ j l → lf j) 
  graft-unit (lf i) = idp
  graft-unit (nd (f , ϕ)) =
    ap (λ x → nd (f , x))
       (Decor-== P (λ j p → graft-unit (ϕ j p)))

  graft-unit-lf-to : {i : I} (w : W P i) (j : I)
    → Leaf P (graft w (λ k _ → lf k)) j
    → Leaf P w j
  graft-unit-lf-to (lf i) j l = l
  graft-unit-lf-to (nd (f , ϕ)) j (k , p , l) =
    k , p , graft-unit-lf-to (ϕ k p) j l

  graft-unit-lf-from : {i : I} (w : W P i) (j : I)
    → Leaf P w j
    → Leaf P (graft w (λ k _ → lf k)) j
  graft-unit-lf-from (lf i) j l = l
  graft-unit-lf-from (nd (f , ϕ)) j (k , p , l) =
    k , p , graft-unit-lf-from (ϕ k p) j l

  graft-unit-lf-to-from : {i : I} (w : W P i) (j : I)
    → (l : Leaf P w j)
    → graft-unit-lf-to w j (graft-unit-lf-from w j l) == l
  graft-unit-lf-to-from (lf i) j l = idp
  graft-unit-lf-to-from (nd (f , ϕ)) j (k , p , l) =
    ap (λ x → (k , p , x)) (graft-unit-lf-to-from (ϕ k p) j l)

  graft-unit-lf-from-to : {i : I} (w : W P i) (j : I)
    → (l : Leaf P (graft w (λ k _ → lf k)) j)
    → graft-unit-lf-from w j (graft-unit-lf-to w j l) == l
  graft-unit-lf-from-to (lf i) j l = idp
  graft-unit-lf-from-to (nd (f , ϕ)) j (k , p , l) =
    ap (λ x → (k , p , x)) (graft-unit-lf-from-to (ϕ k p) j l)

  graft-unit-lf-eqv : {i : I} (w : W P i) (j : I)
    → Leaf P (graft w (λ k _ → lf k)) j
    ≃ Leaf P w j
  graft-unit-lf-eqv w j =
    equiv (graft-unit-lf-to w j) (graft-unit-lf-from w j)
          (graft-unit-lf-to-from w j) (graft-unit-lf-from-to w j)

  graft-unit-lem : {i : I} (w : W P i)
    → (j : I) (l : Leaf P (graft w (λ j l → lf j)) j)
    → graft-unit-lf-to w j l == l [ (λ x → Leaf P x j) ↓ graft-unit w ]
  graft-unit-lem (lf i) j idp = idp
  graft-unit-lem (nd (f , ϕ)) j (k , p , l) = 
    ↓-ap-in (λ x → Leaf P x j) (λ x → nd (f , x)) 
            (↓-nd-Leaf-ih P (λ j p → graft-unit (ϕ j p)) k p
                            (graft-unit-lem (ϕ k p) j l))

  graft-unit-frm : {i : I} {f : Op P i}
    → (w : W P i) (α : Frame P w f)
    → α == (λ j → α j ∘e graft-unit-lf-eqv w j) [ (λ x → Frame P x f) ↓ graft-unit w ]
  graft-unit-frm w α =
    let lem j l₀ l₁ q = –> (α j) l₀
                          =⟨ to-transp! q |in-ctx (–> (α j)) ⟩
                        –> (α j) (transport! (λ x → Leaf P x j) (graft-unit w) l₁)
                          =⟨ ! (to-transp! (graft-unit-lem w j l₁)) |in-ctx (–> (α j)) ⟩
                        –> (α j) (graft-unit-lf-to w j l₁) ∎ 
    in ↓-W-Frame-in P lem

  graft-unit-nd : {i : I} (w : W P i)
    → (g : Ops P) (n : Node P w g)
    → n == graft-node-to w (λ j _ → lf j) g (inl n)
        [ (λ x → Node P x g) ↓ graft-unit w ]
  graft-unit-nd (lf i) g (lift ())
  graft-unit-nd (nd (f , ϕ)) .(_ , f) (inl idp) =
    ↓-ap-in (λ x → Node P x (_ , f)) (λ x → nd (f , x))
      (↓-Node-here-in P (Decor-== P (λ j p → graft-unit (ϕ j p))))
  graft-unit-nd (nd (f , ϕ)) g (inr (k , p , n)) = 
    ↓-ap-in (λ x → Node P x g) (λ x → nd (f , x))
      (↓-Node-there-in P (λ j p → graft-unit (ϕ j p)) k p
        (graft-unit-nd (ϕ k p) g n))
      
  -- grafting is associative
  graft-assoc : {i : I} (w : W P i)
    → (ψ₀ : ∀ j → Leaf P w j → W P j)
    → (ψ₁ : ∀ k → (t : Σ I (λ j → Σ (Leaf P w j) (λ l → Leaf P (ψ₀ j l) k))) → W P k)
    → graft (graft w ψ₀) (λ j l → ψ₁ j (graft-leaf-from w ψ₀ j l)) ==
      graft w (λ j l₀ → graft (ψ₀ j l₀) (λ k l₁ → ψ₁ k (j , l₀ , l₁)))
  graft-assoc (lf i) ψ₀ ψ₁ = idp
  graft-assoc (nd (f , ϕ)) ψ₀ ψ₁ = ap (λ x → nd (f , x))
    (λ= (λ j → λ= (λ p → graft-assoc (ϕ j p) (λ k l → ψ₀ k (j , p , l))
      (λ k t → ψ₁ k (fst t , (j , p , fst (snd t)) , snd (snd t))))))

  -- The associativity path over associated to leaves
  graft-assoc-lf-ovr : {i : I} (w : W P i)
    → (ψ₀ : ∀ j → Leaf P w j → W P j)
    → (ψ₁ : ∀ k → (t : Σ I (λ j → Σ (Leaf P w j) (λ l → Leaf P (ψ₀ j l) k))) → W P k)
    → (j₀ : I) (l₀ : Leaf P w j₀) (j₁ : I) (l₁ : Leaf P (ψ₀ j₀ l₀) j₁)
    → (j₂ : I) (l₂ : Leaf P (ψ₁ j₁ (j₀ , l₀ , l₁)) j₂)
    → graft-lf-to {w = graft w ψ₀} (j₁ , graft-lf-to {w = w} (j₀ , l₀ , l₁) ,
        transport! (λ x → Leaf P (ψ₁ j₁ x) j₂) (graft-leaf-from-to w ψ₀ j₁ (j₀ , l₀ , l₁)) l₂)
      == graft-lf-to {w = w} (j₀ , l₀ , (graft-lf-to {w = ψ₀ j₀ l₀} (j₁ , l₁ , l₂)))
        [ (λ x → Leaf P x j₂) ↓ graft-assoc w ψ₀ ψ₁ ]
  graft-assoc-lf-ovr (lf i) ψ₀ ψ₁ .i idp j₁ l₁ j₂ l₂ = idp
  graft-assoc-lf-ovr (nd (f , ϕ)) ψ₀ ψ₁ j₀ (k , p , l₀) j₁ l₁ j₂ l₂ =
    let H j p = graft-assoc (ϕ j p) (λ k l → ψ₀ k (j , p , l))
                            (λ k t → ψ₁ k (fst t , (j , p , fst (snd t)) , snd (snd t)))
        
        ψ₀' j l = ψ₀ j (k , p , l)
        ψ₁' j t = ψ₁ j (fst t , (k , p , fst (snd t)) , snd (snd t))

        g x = fst x , (k , p , fst (snd x)) , snd (snd x)
        q = graft-leaf-from-to (ϕ k p) ψ₀' j₁ (j₀ , l₀ , l₁)

    in ↓-ap-in (λ x → Leaf P x j₂) (λ x → nd (f , x))
               (↓-nd-Leaf-ih P H k p (ap (λ x → graft-lf-to (j₁ , graft-lf-to (j₀ , l₀ , l₁) , x))
                                          (! (transp!-ap (λ x → Leaf P (ψ₁ j₁ x) j₂) g q l₂)) ∙ᵈ
                                      graft-assoc-lf-ovr (ϕ k p) ψ₀' ψ₁' j₀ l₀ j₁ l₁ j₂ l₂))


  -- -- Okay, my new idea is to write three mutually recursive routines
  -- -- which express the various possibilities individually
  -- graft-assoc-nd-left : {i : I} (w : W P i)
  --   → (ψ₀ : ∀ j → Leaf P w j → W P j)
  --   → (ψ₁ : ∀ k → (t : Σ I (λ j → Σ (Leaf P w j) (λ l → Leaf P (ψ₀ j l) k))) → W P k)
  --   → (g : Ops P) (n : Node P w g)
  --   →  graft-nd-to {w = graft w ψ₀} (inl (graft-nd-to {w = w} (inl n)))
  --   == graft-nd-to {w = w} (inl n) [ (λ x → Node P x g) ↓ graft-assoc w ψ₀ ψ₁ ]
  -- graft-assoc-nd-left w ψ₀ ψ₁ g n = {!!}

  -- graft-assoc-nd-mid : {i : I} (w : W P i)
  --   → (ψ₀ : ∀ j → Leaf P w j → W P j)
  --   → (ψ₁ : ∀ k → (t : Σ I (λ j → Σ (Leaf P w j) (λ l → Leaf P (ψ₀ j l) k))) → W P k)
  --   → (g : Ops P) (j : I) (l : Leaf P w j) (n : Node P (ψ₀ j l) g)
  --   →  graft-nd-to {w = graft w ψ₀} (inl (graft-nd-to {w = w} (inr (j , l , n))))
  --   == graft-nd-to {w = w} (inr (j  , l , graft-nd-to {w = ψ₀ j l} (inl n)))
  --       [ (λ x → Node P x g) ↓ graft-assoc w ψ₀ ψ₁ ]
  -- graft-assoc-nd-mid w ψ₀ ψ₁ g n = {!!}

  -- graft-assoc-nd-right : {i : I} (w : W P i)
  --   → (ψ₀ : ∀ j → Leaf P w j → W P j)
  --   → (ψ₁ : ∀ k → (t : Σ I (λ j → Σ (Leaf P w j) (λ l → Leaf P (ψ₀ j l) k))) → W P k)
  --   → (g : Ops P) (j : I) (l₀ : Leaf P w j)
  --   → (k : I) (l₁ : Leaf P (ψ₀ j l₀) k) (n : Node P (ψ₁ k (j , l₀ , l₁)) g)
  --   → graft-nd-to {w = graft w ψ₀} (inr (k , graft-lf-to {w = w} (j , l₀ , l₁) ,
  --       transport! (λ x → Node P (ψ₁ k x) g) (graft-leaf-from-to w ψ₀ k (j , l₀ , l₁)) n))
  --   == graft-nd-to {w = w} (inr (j , l₀ , graft-nd-to {w = ψ₀ j l₀} (inr (k , l₁ , n))))
  --       [ (λ x → Node P x g) ↓ graft-assoc w ψ₀ ψ₁ ]
  -- graft-assoc-nd-right = {!!}

  -- -- The action of graft associativity on leaves
  -- graft-assoc-lf-action : {i : I} (w : W P i)
  --   → (ψ₀ : ∀ j → Leaf P w j → W P j)
  --   → (ψ₁ : ∀ k → (t : Σ I (λ j → Σ (Leaf P w j) (λ l → Leaf P (ψ₀ j l) k))) → W P k)
  --   → (j : I)
  --   → Leaf P (graft (graft w ψ₀) (λ j l → ψ₁ j (graft-leaf-from w ψ₀ j l))) j
  --   → Leaf P (graft w (λ j l₀ → graft (ψ₀ j l₀) (λ k l₁ → ψ₁ k (j , l₀ , l₁)))) j
  -- graft-assoc-lf-action w ψ₀ ψ₁ j l = 
  --   let (k₁ , l₀₁ , l₂) = graft-leaf-from (graft w ψ₀) (λ j l → ψ₁ j (graft-leaf-from w ψ₀ j l)) j l
  --       (k₀ , l₀ , l₁) = graft-leaf-from w ψ₀ k₁ l₀₁ 
  --   in graft-leaf-to w (λ j l₀ → graft (ψ₀ j l₀) (λ k l₁ → ψ₁ k (j , l₀ , l₁))) j
  --                      (k₀ , l₀ , graft-leaf-to (ψ₀ k₀ l₀) (λ k' l' → ψ₁ k' (k₀ , l₀ , l')) j (k₁ , l₁ , l₂))

  -- -- The path over associated to the above action
  -- graft-assoc-lf-ovr : {i : I} (w : W P i)
  --   → (ψ₀ : ∀ j → Leaf P w j → W P j)
  --   → (ψ₁ : ∀ k → (t : Σ I (λ j → Σ (Leaf P w j) (λ l → Leaf P (ψ₀ j l) k))) → W P k)
  --   → (j : I) (l : Leaf P (graft (graft w ψ₀) (λ j l → ψ₁ j (graft-leaf-from w ψ₀ j l))) j)
  --   → l == graft-assoc-lf-action w ψ₀ ψ₁ j l [ (λ x → Leaf P x j) ↓ graft-assoc w ψ₀ ψ₁ ]
  -- graft-assoc-lf-ovr (lf i) ψ₀ ψ₁ j l =
  --   let w = ψ₀ i idp
  --       ψ j₀ l₀ = ψ₁ j₀ (i , idp , l₀)
  --   in ! (<–-inv-r (graft-leaf-eqv w ψ j) l)
  -- graft-assoc-lf-ovr (nd (f , ϕ)) ψ₀ ψ₁ j (k , p , l) =
  --   let H j p = graft-assoc (ϕ j p) (λ k l → ψ₀ k (j , p , l))
  --                           (λ k t → ψ₁ k (fst t , (j , p , fst (snd t)) , snd (snd t)))
  --       ψ₀' j' l' = ψ₀ j' (k , p , l')
  --       ψ₁' k' t' = let (a , b , c) = t' in ψ₁ k' (a , (k , p , b) , c)
  --   in ↓-ap-in (λ x → Leaf P x j) (λ x → nd (f , x))
  --              (↓-nd-Leaf-ih P H k p (graft-assoc-lf-ovr (ϕ k p) ψ₀' ψ₁' j l))




  -- -- -- The action of associtativity on nodes.
  -- -- module GraftNodeAssocAction {i : I} (w : W P i)
  -- --   (ψ₀ : ∀ j → Leaf P w j → W P j)
  -- --   (ψ₁ : ∀ k → (t : Σ I (λ j → Σ (Leaf P w j) (λ l → Leaf P (ψ₀ j l) k))) → W P k)
  -- --   (g : Ops P) (n : Node P (graft (graft w ψ₀) (λ j l → ψ₁ j (graft-leaf-from w ψ₀ j l))) g) where

  -- --   action-l₀ : Node P (graft w ψ₀) g
  -- --     → Node P (graft w (λ j l₀ → graft (ψ₀ j l₀) (λ k l₁ → ψ₁ k (j , l₀ , l₁)))) g
  -- --   action-l₀ = graft-node-rec {w = w} graft-nd-inl (λ j l n → graft-nd-inr (j , l , graft-nd-inl n))

  -- --   action-lf : (j : I) (k : I) (l₀ : Leaf P w k) (l₁ : Leaf P (ψ₀ k l₀) j)
  -- --     → Node P (ψ₁ j (graft-leaf-from w ψ₀ j (graft-leaf-to w ψ₀ j (k , l₀ , l₁)))) g
  -- --     → Node P (graft w (λ j₁ l₂ → graft (ψ₀ j₁ l₂) (λ k₁ l₃ → ψ₁ k₁ (j₁ , l₂ , l₃)))) g
  -- --   action-lf j k l₀ l₁ n =
  -- --     let n' = transport (λ x → Node P (ψ₁ j x) g) (graft-leaf-from-to w ψ₀ j (k , l₀ , l₁)) n
  -- --     in graft-nd-inr {w = w} (k , l₀ , (graft-nd-inr {w = ψ₀ k l₀} (j , l₁ , n')))

  -- --   action-r-fib : (j : I) (l : Leaf P (graft w ψ₀) j) → Type ℓ
  -- --   action-r-fib j l = Node P (ψ₁ j (graft-leaf-from w ψ₀ j l)) g
  -- --     → Node P (graft w (λ j₁ l₀ → graft (ψ₀ j₁ l₀) (λ k l₁ → ψ₁ k (j₁ , l₀ , l₁)))) g
  
  -- --   action-r₀ : (j : I) (l : Leaf P (graft w ψ₀) j) → action-r-fib j l
  -- --   action-r₀ j = graft-lf-elim {w = w} (action-r-fib j) (action-lf j)

  -- -- graft-assoc-nd-action : {i : I} (w : W P i)
  -- --   → (ψ₀ : ∀ j → Leaf P w j → W P j)
  -- --   → (ψ₁ : ∀ k → (t : Σ I (λ j → Σ (Leaf P w j) (λ l → Leaf P (ψ₀ j l) k))) → W P k)
  -- --   → (g : Ops P)
  -- --   → Node P (graft (graft w ψ₀) (λ j l → ψ₁ j (graft-leaf-from w ψ₀ j l))) g
  -- --   → Node P (graft w (λ j l₀ → graft (ψ₀ j l₀) (λ k l₁ → ψ₁ k (j , l₀ , l₁)))) g
  -- -- graft-assoc-nd-action w ψ₀ ψ₁ g n =
  -- --   graft-node-rec {w = graft w ψ₀} action-l₀ action-r₀ n
  -- --   where open GraftNodeAssocAction w ψ₀ ψ₁ g n

  -- -- -- The associated path over
  -- -- graft-assoc-nd-ovr : {i : I} (w : W P i)
  -- --   → (ψ₀ : ∀ j → Leaf P w j → W P j)
  -- --   → (ψ₁ : ∀ k → (t : Σ I (λ j → Σ (Leaf P w j) (λ l → Leaf P (ψ₀ j l) k))) → W P k)
  -- --   → (g : Ops P)
  -- --   → (n : Node P (graft (graft w ψ₀) (λ j l → ψ₁ j (graft-leaf-from w ψ₀ j l))) g)
  -- --   → n == graft-assoc-nd-action w ψ₀ ψ₁ g n [ (λ x → Node P x g) ↓ graft-assoc w ψ₀ ψ₁ ]
  -- -- graft-assoc-nd-ovr (lf i) ψ₀ ψ₁ g n =
  -- --   graft-node-elim {w = ψ₀ i idp} Q lf-inl lf-inr n

  -- --   where open GraftNodeAssocAction (lf i) ψ₀ ψ₁ g n

  -- --         Q : Node P (graft (ψ₀ i idp) (λ j l → ψ₁ j (graft-leaf-from (lf i) ψ₀ j l))) g → Type ℓ
  -- --         Q n = n == graft-assoc-nd-action (lf i) ψ₀ ψ₁ g n

  -- --         lf-inl : (n : Node P (ψ₀ i idp) g) → Q (graft-nd-inl n)
  -- --         lf-inl n = graft-nd-inl n
  -- --                      =⟨ ! (graft-node-rec-inl-β action-l₀ action-r₀ n) ⟩ 
  -- --                    graft-node-rec action-l₀ action-r₀ (graft-nd-inl n) ∎

  -- --         lf-inr : (j : I) (l : Leaf P (ψ₀ i idp) j) (n : Node P (ψ₁ j (i , idp , l)) g) → Q (graft-nd-inr (j , l , n))
  -- --         lf-inr j l n = graft-nd-inr (j , l , n)
  -- --                          =⟨ ! (graft-node-rec-inr-β action-l₀ action-r₀ j l n) ⟩
  -- --                        graft-node-rec action-l₀ action-r₀ (graft-nd-inr (j , l , n)) ∎

  -- -- graft-assoc-nd-ovr (nd (f , ϕ)) ψ₀ ψ₁ ._ (inl idp) =
  -- --   let H j p = graft-assoc (ϕ j p) (λ k l → ψ₀ k (j , p , l))
  -- --                  (λ k t → ψ₁ k (fst t , (j , p , fst (snd t)) , snd (snd t)))
  -- --   in ↓-ap-in (λ x → Node P x (_ , f)) (λ x → nd (f , x))
  -- --              (↓-Node-here-in P (λ= (λ j → λ= (λ p → H j p))))
               
  -- -- graft-assoc-nd-ovr (nd (f , ϕ)) ψ₀ ψ₁ g (inr (j , p , n)) = 
  -- --   let H j₀ p₀ = graft-assoc (ϕ j₀ p₀) (ψ₀' j₀ p₀) (ψ₁' j₀ p₀)
  -- --       ih = graft-assoc-nd-ovr (ϕ j p) (ψ₀' j p) (ψ₁' j p) g n
  -- --   in ↓-ap-in (λ x → Node P x g) (λ x → nd (f , x))
  -- --              (↓-Node-there-in P H j p ih ∙'ᵈ {!!} ∙ claim) 

  -- --   where ψ₀' : (j₀ : I) (p₀ : Param P f j₀) (j₁ : I) (l₁ : Leaf P (ϕ j₀ p₀) j₁) → W P j₁
  -- --         ψ₀' j₀ p₀ j₁ l₁ = ψ₀ j₁ (j₀ , p₀ , l₁)

  -- --         ψ₁' : (j₀ : I) (p₀ : Param P f j₀) (j₁ : I)
  -- --           → (t : Σ I (λ v → Σ (Leaf P (ϕ j₀ p₀) v) (λ l → Leaf P (ψ₀ v (j₀ , p₀ , l)) j₁)))
  -- --           →  W P j₁
  -- --         ψ₁' j₀ p₀ j₁ t = ψ₁ j₁ (fst t , (j₀ , p₀ , fst (snd t)) , snd (snd t))

  -- --         ϕg : (j : I) → Param P f j → W P j
  -- --         ϕg j p = graft (ϕ j p) (ψ₀' j p)

  -- --         ψg : (j : I) → Σ I (λ k → Σ (Param P f k) (λ p → Leaf P (ϕg k p) j)) → W P j
  -- --         ψg j l = ψ₁ j (graft-leaf-from (nd (f , ϕ)) ψ₀ j l)

  -- --         w : W P j
  -- --         w = graft (ϕ j p) (ψ₀' j p)

  -- --         ψw : (k : I) (l : Leaf P w k) → W P k
  -- --         ψw k l = ψ₁' j p k (graft-leaf-from (ϕ j p) (ψ₀' j p) k l)

  -- --         module S = GraftNodeAssocAction (nd (f , ϕ)) ψ₀ ψ₁ g (inr (j , p , n))
          
  -- --         claim : graft-node-rec {w = w} (λ n₁ → S.action-l₀ (inr (j , p , n₁))) (λ k l n₁ → S.action-r₀ k (j , p , l) n₁) n
  -- --             == graft-assoc-nd-action (nd (f , ϕ)) ψ₀ ψ₁ g (inr (j , p , n))
  -- --         claim = graft-node-rec-unfold S.action-l₀ S.action-r₀ j p n

  -- --         Q : Node P (graft w ψw) g → Type ℓ
  -- --         Q n = inr (j , p , graft-assoc-nd-action (ϕ j p) (ψ₀' j p) (ψ₁' j p) g n)
  -- --               == graft-node-rec {w = w} (λ n₁ → S.action-l₀ (inr (j , p , n₁))) (λ k l n₁ → S.action-r₀ k (j , p , l) n₁) n

  -- --         nd-inl : (n₀ : Node P w g) → Q (graft-nd-inl n₀)
  -- --         nd-inl n₀ = {!!}

  -- -- --         nd-inl : (n₀ : Node P w g) → Q (graft-node-to w ψw g (inl n₀))
  -- -- --         nd-inl n₀ = inr (j , p , graft-assoc-nd-action (ϕ j p) (ψ₀' j p) (ψ₁'' j p) g n₁)
  -- -- --                       =⟨ <–-inv-l (graft-node-eqv w ψw g) (inl n₀)
  -- -- --                          |in-ctx (λ x → inr (j , p , ⊔-rec N.inl₀ N.inr₀ x)) ⟩
  -- -- --                     inr (j , p , ⊔-rec (N.inl₁ n₀) (N.inr₁ n₀) (graft-node-from (ϕ j p) (ψ₀' j p) g n₀))
  -- -- --                       =⟨ {!!} ⟩ 
  -- -- --                     ⊔-rec (M.inl₁ (inr (j , p , n₀))) (M.inr₁ (inr (j , p , n₀)))
  -- -- --                       (graft-node-from-lcl f ϕ ψ₀ g j p (graft-node-from (ϕ j p) (ψ₀' j p) g n₀))
  -- -- --                       =⟨ ! (<–-inv-l (graft-node-eqv w ψw g) (inl n₀))
  -- -- --                           |in-ctx (λ x → ⊔-rec M.inl₀ M.inr₀ (graft-node-from-lcl f ϕg ψg g j p x)) ⟩ 
  -- -- --                     ⊔-rec M.inl₀ M.inr₀ (graft-node-from-lcl f ϕg ψg g j p (graft-node-from w ψw g n₁)) ∎

  -- -- --           where n₁ : Node P (graft w ψw) g
  -- -- --                 n₁ = graft-node-to w ψw g (inl n₀)

  -- -- --                 module M = GraftNodeAssocAction (nd (f , ϕ)) ψ₀ ψ₁ g (inr (j , p , n₁))
  -- -- --                 module N = GraftNodeAssocAction (ϕ j p) (ψ₀' j p) (ψ₁'' j p) g n₁

  -- -- --                 Q' : Node P w g → Type ℓ
  -- -- --                 Q' nw = inr (j , p , ⊔-rec N.inl₀ N.inr₀ {!!})
  -- -- --                         == ⊔-rec (M.inl₁ (inr (j , p , n₀))) (M.inr₁ (inr (j , p , n₀)))
  -- -- --                              (graft-node-from-lcl f ϕ ψ₀ g j p
  -- -- --                                (graft-node-from (ϕ j p) (ψ₀' j p) g nw))


  -- -- --                 nd-inl₁ : (nl : Node P (ϕ j p) g) → Q' (graft-node-to (ϕ j p) (ψ₀' j p) g (inl nl))
  -- -- --                 nd-inl₁ nl = {!!}
  -- -- --                   -- let nt = graft-node-to (ϕ j p) (ψ₀' j p) g (inl nl)
  -- -- --                   -- in inr (j , p , N.inl₀ n₀)
  -- -- --                   --      =⟨ {!!} ⟩
  -- -- --                   --    M.inl₁ (inr (j , p , n₀)) (inr (j , p , nl))
  -- -- --                   --      =⟨ ! (<–-inv-l (graft-node-eqv (ϕ j p) (ψ₀' j p) g) (inl nl))
  -- -- --                   --         |in-ctx (λ x → ⊔-rec (M.inl₁ (inr (j , p , n₀))) (M.inr₁ (inr (j , p , n₀)))
  -- -- --                   --                          (graft-node-from-lcl f ϕ ψ₀ g j p x)) ⟩ 
  -- -- --                   --    ⊔-rec (M.inl₁ (inr (j , p , n₀))) (M.inr₁ (inr (j , p , n₀)))
  -- -- --                   --      (graft-node-from-lcl f ϕ ψ₀ g j p
  -- -- --                   --        (graft-node-from (ϕ j p) (ψ₀' j p) g nt)) ∎

  -- -- --                 nd-inr₁ : (t : Σ I (λ k → Σ (Leaf P (ϕ j p) k) (λ l → Node P (ψ₀ k (j , p , l)) g)))
  -- -- --                   → Q' (graft-node-to (ϕ j p) (ψ₀' j p) g (inr t))
  -- -- --                 nd-inr₁ (k , l , nr) = {!!}

  -- --         nd-inr : (k : I) (l : Leaf P w k) (n₀ : Node P (ψw k l) g) → Q (graft-nd-inr (k , l , n₀))
  -- --         nd-inr k l n₀ = 
  -- --           let module N = GraftNodeAssocAction (ϕ j p) (ψ₀' j p) (ψ₁' j p) g (graft-nd-inr (k , l , n₀))
  -- --           in inr (j , p , graft-assoc-nd-action (ϕ j p) (ψ₀' j p) (ψ₁' j p) g (graft-nd-inr (k , l , n₀)))
  -- --                =⟨ {!!} ⟩ 
  -- --              graft-lf-elim {w = ϕ j p} (λ l₀ → S.action-r-fib k (j , p , l₀)) (λ k' l₀ l₁ → S.action-lf k k' (j , p , l₀) l₁) l n₀
  -- --                =⟨ app= (graft-lf-elim-unfold (S.action-r-fib k) (S.action-lf k) j p l) n₀ ⟩
  -- --              graft-lf-elim {w = nd (f , ϕ)} (S.action-r-fib k) (S.action-lf k) (j , p , l) n₀
  -- --                =⟨ ! (graft-node-rec-inr-β (λ n₁ → S.action-l₀ (inr (j , p , n₁))) (λ x y z → S.action-r₀ x (j , p , y) z) k l n₀) ⟩ 
  -- --              graft-node-rec {w = w} (λ n₁ → S.action-l₀ (inr (j , p , n₁))) (λ x y z → S.action-r₀ x (j , p , y) z) (graft-nd-inr (k , l , n₀)) ∎


  -- --   -- graft-lf-elim-unfold : ∀ {ℓ'} {i : I} {f : Op P i}
  -- --   --   → {ϕ : ∀ j → Param P f j → W P j}
  -- --   --   → {ψ : ∀ j → Leaf P (nd (f , ϕ)) j → W P j} {j : I}
  -- --   --   → (Q : (l : Leaf P (graft (nd (f , ϕ)) ψ) j) → Type ℓ')
  -- --   --   → (σ : (k : I) (l₀ : Leaf P (nd (f , ϕ)) k) (l₁ : Leaf P (ψ k l₀) j)
  -- --   --        → Q (graft-leaf-to (nd (f , ϕ)) ψ j (k , l₀ , l₁) ))
  -- --   --   → (k : I) (p : Param P f k) (l : Leaf P (graft (ϕ k p) (λ k' l → ψ k' (k , p , l))) j)
  -- --   --   → graft-lf-elim {w = ϕ k p} (λ l₀ → Q (k , p , l₀)) (λ k' l₀ l₁ → σ k' (k , p , l₀) l₁) l
  -- --   --     == graft-lf-elim Q σ (k , p , l)



  -- --         -- module S = GraftNodeAssocAction (nd (f , ϕ)) ψ₀ ψ₁ g (inr (j , p , n))

  -- --   -- action-r₀ : (j : I) (l : Leaf P (graft w ψ₀) j)
  -- --   --   → Node P (ψ₁ j (graft-leaf-from w ψ₀ j l)) g
  -- --   --   → Node P (graft w (λ j₁ l₀ → graft (ψ₀ j₁ l₀) (λ k l₁ → ψ₁ k (j₁ , l₀ , l₁)))) g
  -- --   -- action-r₀ j = graft-lf-elim {w = w} _ (action-lf j)

  -- -- -- graft-node-to : {i : I} (w : W P i)
  -- -- --   → (ψ : ∀ j → Leaf P w j → W P j) (g : Ops P)
  -- -- --   → Node P w g ⊔ Σ I (λ k → Σ (Leaf P w k) (λ l → Node P (ψ k l) g))
  -- -- --   → Node P (graft w ψ) g
  -- -- -- graft-node-to (lf i) ψ g (inl ())
  -- -- -- graft-node-to (lf i) ψ g (inr (.i , idp , n)) = n
  -- -- -- graft-node-to (nd (f ,  ϕ)) ψ ._ (inl (inl idp)) = inl idp
  -- -- -- graft-node-to (nd (f ,  ϕ)) ψ g (inl (inr (j , p , n))) =
  -- -- --   inr (j , p , graft-node-to (ϕ j p) (λ k l → ψ k (j , p , l)) g (inl n))
  -- -- -- graft-node-to (nd (f ,  ϕ)) ψ g (inr (k , (j , p , l) , n)) = 
  -- -- --   inr (j , p , graft-node-to (ϕ j p) (λ k l → ψ k (j , p , l)) g (inr (k , l , n)))




  -- -- --         nd-inr : (t : Σ I (λ k → Σ (Leaf P w k) (λ l → Node P (ψw k l) g))) → Q (graft-node-to w ψw g (inr t))
  -- -- --         nd-inr (k , l , n₀) = 
  -- -- --           let n₁ = graft-node-to w ψw g (inr (k , l , n₀))
  -- -- --               module M = GraftNodeAssocAction (nd (f , ϕ)) ψ₀ ψ₁ g (inr (j , p , n₁))
  -- -- --               module N = GraftNodeAssocAction (ϕ j p) (ψ₀' j p) (ψ₁'' j p) g n₁
  -- -- --           in inr (j , p , graft-assoc-nd-action (ϕ j p) (ψ₀' j p) (ψ₁'' j p) g n₁)
  -- -- --                =⟨ <–-inv-l (graft-node-eqv w ψw g) (inr (k , l , n₀))
  -- -- --                    |in-ctx (λ x → inr (j , p , ⊔-rec N.inl₀ N.inr₀ x)) ⟩
  -- -- --              inr (j , p , N.inr₀ (k , l , n₀))
  -- -- --                =⟨ ! (<–-inv-l (graft-node-eqv w ψw g) (inr (k , l , n₀)))
  -- -- --                    |in-ctx (λ x → ⊔-rec M.inl₀ M.inr₀ (graft-node-from-lcl f ϕg ψg g j p x)) ⟩ 
  -- -- --              ⊔-rec M.inl₀ M.inr₀ (graft-node-from-lcl f ϕg ψg g j p (graft-node-from w ψw g n₁)) ∎


  
