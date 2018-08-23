{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util

module Polynomial where

  record Poly (I : Type₀) : Type₁ where
    field
      γ : I → Type₀
      ρ : {i : I} (c : γ i) (j : I) → Type₀

  open Poly public

  ⟦_⟧ : {I : Type₀} (P : Poly I) → (I → Set) → I → Set
  ⟦ P ⟧ X i = Σ (γ P i) (λ c → ∀ j → (p : ρ P c j) → X j)

  module _ {I : Type₀} (P : Poly I) where
  
    data W : I → Type₀ where
      lf : (i : I) → W i
      nd : {i : I} → ⟦ P ⟧ W i → W i

    data Leaf : {i : I} (w : W i) → I → Type₀ where
      leaf : (i : I) → Leaf (lf i) i
      stem : {i : I} {c : γ P i}
        → {δ : ∀ j → (p : ρ P c j) → W j}
        → {j : I} → (p : ρ P c j)
        → {k : I} → Leaf (δ j p) k
        → Leaf (nd (c , δ)) k

    lf-lf-contr : (i : I) → is-contr (Σ I (Leaf (lf i)))
    lf-lf-contr i = has-level-in ((i , leaf i) , λ { (_ , leaf .i) → idp })

    lf-inv : {i j : I} (p : i == j) (w : W i)
      → ∀ k → Leaf w k ≃ Leaf (transport W p w) k
    lf-inv idp w k = ide (Leaf w k)
    
    lf-elim : {i : I} (Q : ∀ j → Leaf (lf i) j → Type₀)
      → (d : Q i (leaf i))
      → (j : I) → (l : Leaf (lf i) j) → Q j l
    lf-elim Q d j (leaf .j) = d
      
    data Node : {i : I} (w : W i) {j : I} (c : γ P j) → Type₀ where
      this : {i : I} {c : γ P i}
        → {δ : ∀ j → (p : ρ P c j) → W j}
        → Node (nd (c , δ)) c
      that : {i : I} {c : γ P i}
        → {δ : ∀ j → (p : ρ P c j) → W j}
        → {j : I} → (p : ρ P c j)
        → {k : I} → {d : γ P k} → Node (δ j p) d
        → Node (nd (c , δ)) d

    nd-inv : {i j : I} (p : i == j) (w : W i)
      → ∀ {k} → (d : γ P k) → Node w d ≃ Node (transport W p w) d
    nd-inv idp w d = ide (Node w d)
    
    corolla : {i : I} (c : γ P i) → W i
    corolla {i} c = nd (c , λ j p → lf j)

    corolla-lf-eqv : {i : I} (c : γ P i)
      → (j : I) → Leaf (corolla c) j ≃ ρ P c j
    corolla-lf-eqv c j = equiv to from (λ _ → idp) from-to

      where to : Leaf (corolla c) j → ρ P c j
            to (stem p (leaf i)) = p

            from : ρ P c j → Leaf (corolla c) j
            from p = stem p (leaf j)

            from-to : (l : Leaf (corolla c) j) → from (to l) == l
            from-to (stem p (leaf i)) = idp

  --
  --  Frames and FillingFamilies
  --
  
  Frame : {I : Type₀} (P : Poly I) {i : I} (w : W P i) (c : γ P i) → Type₀
  Frame {I} P w c = (j : I) → Leaf P w j ≃ ρ P c j

  FillingFamily : {I : Type₀} → Poly I → Type₁
  FillingFamily {I} P = {i : I} (w : W P i) (c : γ P i) → Frame P w c → Type₀

  _//_ : {I : Type₀} (P : Poly I) (F : FillingFamily P) → Poly (Σ I (γ P))
  γ (P // F) (i , c) = Σ (W P i) (λ w → Σ (Frame P w c) (F w c))
  ρ (P // F) (w , f , x) (j , d) = Node P w d

  filler-inv : {I : Type₀} {P : Poly I} (F : FillingFamily P)
    → {i : I} {w₀ w₁ : W P i} (p : w₀ == w₁)
    → (c : γ P i) → Σ (Frame P w₀ c) (F w₀ c) ≃ Σ (Frame P w₁ c) (F w₁ c)
  filler-inv F idp c = ide _

  --
  --  Polynomial Domains
  --
  
  record PolyDomain {I : Type₀} (P : Poly I) : Type₁ where
    coinductive
    field

      F : FillingFamily P 
      H : PolyDomain (P // F)

  open PolyDomain public

  --
  --  Grafting of trees
  --

  module _ {I : Type₀} (P : Poly I) where

    Fr : Poly I
    γ Fr = W P
    ρ Fr w = Leaf P w

    graft : {i : I} (w : W P i) (ε : ∀ j → Leaf P w j → W P j) → W P i
    graft (lf i) ε = ε i (leaf i)
    graft (nd (c , δ)) ε =
      let ε' j p k l = ε k (stem p l)
          δ' j p = graft (δ j p) (ε' j p)
      in nd (c , δ')

    --
    --  Leaves in a graft
    --

    graft-leaf-to : {i : I} (w : W P i) (ε : ∀ j → Leaf P w j → W P j) (k : I)
      → Leaf P (graft w ε) k
      → Σ I (λ j → Σ (Leaf P w j) (λ l → Leaf P (ε j l) k))
    graft-leaf-to (lf i) ε k l = i , leaf i , l
    graft-leaf-to (nd (c , δ)) ε k (stem p l) = 
      let (s , t , u) = graft-leaf-to (δ _ p) (λ k l → ε k (stem p l)) k l
      in s , stem p t , u

    graft-leaf-from : {i : I} (w : W P i) (ε : ∀ j → Leaf P w j → W P j) (k : I)
      → Σ I (λ j → Σ (Leaf P w j) (λ l → Leaf P (ε j l) k))
      → Leaf P (graft w ε) k
    graft-leaf-from (lf i) ε k (.i , leaf .i , l) = l
    graft-leaf-from (nd (c , δ)) ε k (j , stem p l₀ , l₁) = 
      let ε' j p k l = ε k (stem p l)
          δ' j p = graft (δ j p) (ε' j p)
      in stem p (graft-leaf-from (δ _ p) (ε' _ p) k (j , l₀ , l₁))

    abstract
    
      graft-leaf-to-from : {i : I} (w : W P i) (ε : ∀ j → Leaf P w j → W P j) (k : I)
        → (l : Σ I (λ j → Σ (Leaf P w j) (λ l → Leaf P (ε j l) k)))
        → graft-leaf-to w ε k (graft-leaf-from w ε k l) == l
      graft-leaf-to-from (lf i) ε k (.i , leaf .i , l₁) = idp
      graft-leaf-to-from (nd (c , δ)) ε k (j , stem p l₀ , l₁) =
        let ε' j p k l = ε k (stem p l)
            δ' j p = graft (δ j p) (ε' j p)
            (s , t , u) = graft-leaf-to (δ _ p) (ε' _ p) k
                            (graft-leaf-from (δ _ p) (ε' _ p) k (j , l₀ , l₁))
            ih = graft-leaf-to-from (δ _ p) (ε' _ p) k (j , l₀ , l₁)
        in pair= (fst= ih) (apd↓-cst (λ x → (stem p (fst x) , snd x)) (snd= ih)) 

      graft-leaf-from-to : {i : I} (w : W P i) (ε : ∀ j → Leaf P w j → W P j)
        → (k : I) (l : Leaf P (graft w ε) k)
        → graft-leaf-from w ε k (graft-leaf-to w ε k l) == l
      graft-leaf-from-to (lf i) ε k l = idp
      graft-leaf-from-to (nd (c , δ)) ε k (stem p l) =
        let ε' j p k l = ε k (stem p l)
            δ' j p = graft (δ j p) (ε' j p)
        in ap (λ x → stem p x) (graft-leaf-from-to (δ _ p) (ε' _ p) k l) 

    graft-leaf-eqv : {i : I} (w : W P i) (ε : ∀ j → Leaf P w j → W P j) (k : I)
      → Leaf P (graft w ε) k
        ≃ Σ I (λ j → Σ (Leaf P w j) (λ l → Leaf P (ε j l) k))
    graft-leaf-eqv w ε k =
      equiv (graft-leaf-to w ε k) (graft-leaf-from w ε k)
            (graft-leaf-to-from w ε k) (graft-leaf-from-to w ε k)

    --
    --  Nodes in a graft
    --

    graft-node-to : {i : I} (w : W P i)
      → (ε : ∀ j → Leaf P w j → W P j)
      → {j : I} (c : γ P j)
      → Node P w c ⊔ Σ I (λ k → Σ (Leaf P w k) (λ l → Node P (ε k l) c))
      → Node P (graft w ε) c
    graft-node-to (lf i) ε c₀ (inl ())
    graft-node-to (lf i) ε c₀ (inr (.i , leaf .i , n)) = n
    graft-node-to (nd (c , δ)) ε .c (inl this) = this
    graft-node-to (nd (c , δ)) ε c₀ (inl (that p n)) =
      that p (graft-node-to (δ _ p) (λ k l → ε k (stem p l)) c₀ (inl n))
    graft-node-to (nd (c , δ)) ε c₀ (inr (k , stem p l , n)) = 
      that p (graft-node-to (δ _ p) (λ k l → ε k (stem p l)) c₀ (inr (k , l , n)))

    graft-node-from : {i : I} (w : W P i)
      → (ε : ∀ j → Leaf P w j → W P j)
      → {j : I} (c : γ P j)
      → Node P (graft w ε) c
      → Node P w c ⊔ Σ I (λ k → Σ (Leaf P w k) (λ l → Node P (ε k l) c))
    graft-node-from (lf i) ε c₀ n = inr (i , leaf i , n)
    graft-node-from (nd (c , δ)) ε .c this = inl this
    graft-node-from (nd (c , δ)) ε c₀ (that p n) with graft-node-from (δ _ p) (λ k l → ε k (stem p l)) c₀ n
    graft-node-from (nd (c , δ)) ε c₀ (that p n) | inl n' = inl (that p n')
    graft-node-from (nd (c , δ)) ε c₀ (that p n) | inr (k , l , n') = inr (k , stem p l , n')

    abstract
    
      graft-node-to-from : {i : I} (w : W P i)
        → (ε : ∀ j → Leaf P w j → W P j)
        → {j : I} (c : γ P j)
        → (n : Node P (graft w ε) c)
        → graft-node-to w ε c (graft-node-from w ε c n) == n
      graft-node-to-from (lf i) ε c₀ n = idp
      graft-node-to-from (nd (c , δ)) ε .c this = idp
      graft-node-to-from (nd (c , δ)) ε c₀ (that p n) with
        graft-node-from (δ _ p) (λ k l → ε k (stem p l)) c₀ n |
        inspect (graft-node-from (δ _ p) (λ k l → ε k (stem p l)) c₀) n
      graft-node-to-from (nd (c , δ)) ε c₀ (that p n) | inl n' | ingraph e =
        ap (that p) lem

        where lem = graft-node-to (δ _ p) (λ k l → ε k (stem p l)) c₀ (inl n')
                      =⟨ ! e |in-ctx (graft-node-to (δ _ p) (λ k l → ε k (stem p l)) c₀) ⟩
                    graft-node-to (δ _ p) (λ k l → ε k (stem p l)) c₀
                      (graft-node-from (δ _ p) (λ k l → ε k (stem p l)) c₀ n)
                      =⟨ graft-node-to-from (δ _ p) (λ k l → ε k (stem p l)) c₀ n ⟩ 
                    n ∎

      graft-node-to-from (nd (c , δ)) ε c₀ (that p n) | inr (k , l , n') | ingraph e =
        ap (that p) lem

        where lem = graft-node-to (δ _ p) (λ k l → ε k (stem p l)) c₀ (inr (k , l , n')) 
                      =⟨ ! e |in-ctx (graft-node-to (δ _ p) (λ k l → ε k (stem p l)) c₀) ⟩
                    graft-node-to (δ _ p) (λ k l → ε k (stem p l)) c₀
                      (graft-node-from (δ _ p) (λ k l → ε k (stem p l)) c₀ n)
                      =⟨ graft-node-to-from (δ _ p) (λ k l → ε k (stem p l)) c₀ n ⟩ 
                    n ∎


      graft-node-from-to : {i : I} (w : W P i)
        → (ε : ∀ j → Leaf P w j → W P j)
        → {j : I} (c : γ P j)
        → (n : Node P w c ⊔ Σ I (λ k → Σ (Leaf P w k) (λ l → Node P (ε k l) c)))
        → graft-node-from w ε c (graft-node-to w ε c n) == n
      graft-node-from-to (lf i) ε c₀ (inl ())
      graft-node-from-to (lf i) ε c₀ (inr (.i , leaf .i , n)) = idp
      graft-node-from-to (nd (c , δ)) ε .c (inl this) = idp
      graft-node-from-to (nd (c , δ)) ε c₀ (inl (that p n)) with 
        (graft-node-from (δ _ p) (λ k l → ε k (stem p l)) c₀ ∘ graft-node-to (δ _ p) (λ k l → ε k (stem p l)) c₀) (inl n)
        | inspect (graft-node-from (δ _ p) (λ k l → ε k (stem p l)) c₀ ∘ graft-node-to (δ _ p) (λ k l → ε k (stem p l)) c₀) (inl n)
      graft-node-from-to (nd (c , δ)) ε c₀ (inl (that p n)) | inl n' | ingraph e =
        ap (λ x → inl (that p x)) (–> (inl=inl-equiv n' n) lem)

        where lem = inl n' =⟨ ! e ⟩
                    graft-node-from (δ _ p) (λ k l → ε k (stem p l)) c₀
                      (graft-node-to (δ _ p) (λ k l → ε k (stem p l)) c₀ (inl n))
                      =⟨ graft-node-from-to (δ _ p) (λ k l → ε k (stem p l)) c₀ (inl n) ⟩ 
                    inl n ∎

      graft-node-from-to (nd (c , δ)) ε c₀ (inl (that p n)) | inr (k , l , n') | ingraph e =
        ⊥-elim (inr≠inl (k , l , n') n lem)

        where lem = inr (k , l , n') =⟨ ! e ⟩
                    graft-node-from (δ _ p) (λ k₁ l₁ → ε k₁ (stem p l₁)) c₀
                      (graft-node-to (δ _ p) (λ k₁ l₁ → ε k₁ (stem p l₁)) c₀ (inl n))
                      =⟨ graft-node-from-to (δ _ p) (λ k l → ε k (stem p l)) c₀ (inl n) ⟩ 
                    inl n ∎

      graft-node-from-to (nd (c , δ)) ε c₀ (inr (k , stem p l , n)) with
        (graft-node-from (δ _ p) (λ k l → ε k (stem p l)) c₀ ∘ graft-node-to (δ _ p) (λ k l → ε k (stem p l)) c₀) (inr (k , l , n))
        | inspect (graft-node-from (δ _ p) (λ k l → ε k (stem p l)) c₀ ∘ graft-node-to (δ _ p) (λ k l → ε k (stem p l)) c₀) (inr (k , l , n))
      graft-node-from-to (nd (c , δ)) ε c₀ (inr (k , stem p l , n)) | inl n' | ingraph e =
        ⊥-elim (inl≠inr n' (k , l , n) lem)

        where lem = inl n' =⟨ ! e ⟩
                    graft-node-from (δ _ p) (λ k l → ε k (stem p l)) c₀
                      (graft-node-to (δ _ p) (λ k l → ε k (stem p l)) c₀ (inr (k , l , n)))
                      =⟨ graft-node-from-to (δ _ p) (λ k l → ε k (stem p l)) c₀ (inr (k , l , n)) ⟩
                    inr (k , l , n) ∎

      graft-node-from-to (nd (c , δ)) ε c₀ (inr (k , stem p l , n)) | inr (k' , l' , n') | ingraph e =
        let lem' = –> (inr=inr-equiv (k' , l' , n') (k , l , n)) lem
        in ap inr (pair= (fst= lem') (apd↓-cst (λ x → (stem p (fst x) , snd x)) (snd= lem')))

        where lem = inr (k' , l' , n') =⟨ ! e ⟩ 
                    graft-node-from (δ _ p) (λ k l → ε k (stem p l)) c₀
                      (graft-node-to (δ _ p) (λ k l → ε k (stem p l)) c₀ (inr (k , l , n)))
                      =⟨ graft-node-from-to (δ _ p) (λ k l → ε k (stem p l)) c₀ (inr (k , l , n)) ⟩ 
                    inr (k , l , n) ∎
      
    graft-node-eqv : {i : I} (w : W P i)
      → (ε : ∀ j → Leaf P w j → W P j)
      → {j : I} (c : γ P j)
      → Node P w c ⊔ Σ I (λ k → Σ (Leaf P w k) (λ l → Node P (ε k l) c))
        ≃ Node P (graft w ε) c
    graft-node-eqv w ε c =
      equiv (graft-node-to w ε c) (graft-node-from w ε c)
            (graft-node-to-from w ε c) (graft-node-from-to w ε c)

