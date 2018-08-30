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

module Signature where

  record Poly {ℓ} (I : Type ℓ) : Type (lsucc ℓ) where
    field
      Op : I → Type ℓ
      Param : {i : I} → Op i → I → Type ℓ

  open Poly public
  
  ⟦_⟧ : ∀ {ℓ} {I : Type ℓ} (P : Poly I) → (I → Type ℓ) → I → Type ℓ
  ⟦ P ⟧ X i = Σ (Op P i) (λ f → ∀ j → Param P f j → X j)

  module _ {ℓ} {I : Type ℓ} (P : Poly I) where

    data W : I → Type ℓ where
      lf : (i : I) → W i
      nd : {i : I} → ⟦ P ⟧ W i → W i

    Leaf : {i : I} (w : W i) → I → Type ℓ
    Leaf (lf i) j = i == j
    Leaf (nd (f , ϕ)) j = Σ I (λ k → Σ (Param P f k) (λ p → Leaf (ϕ k p) j))

    Node : {i : I} (w : W i) {j : I} → Op P j → Type ℓ
    Node (lf i) p = Lift ⊥
    Node (nd {i} (f , ϕ)) {j} g = ((i , f) == (j , g)) ⊔ Σ I (λ k → Σ (Param P f k) (λ p → Node (ϕ k p) g))

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

    --
    --  Characterizing paths in W-types
    --

    -- W-unfold-eqv : (i : I) → W i ≃ ⊤ ⊔ ⟦ P ⟧ W i
    -- W-unfold-eqv i = equiv to from to-from from-to

    --   where to : W i → ⊤ ⊔ ⟦ P ⟧ W i
    --         to (lf i) = inl tt
    --         to (nd pw) = inr pw

    --         from : ⊤ ⊔ ⟦ P ⟧ W i → W i
    --         from (inl tt) = lf i
    --         from (inr pw) = nd pw

    --         to-from : (w : ⊤ ⊔ ⟦ P ⟧ W i) → to (from w) == w
    --         to-from (inl tt) = idp
    --         to-from (inr pw) = idp

    --         from-to : (w : W i) → from (to w) == w
    --         from-to (lf i) = idp
    --         from-to (nd pw) = idp

    -- Yeah, so this doesn't work because of termination.
    -- W-level : ∀ {n} (op-lvl : (i : I) → has-level (S (S n)) (Op P i)) → (i : I) → has-level (S (S n)) (W i)
    -- W-level op-lvl i = equiv-preserves-level ((W-unfold-eqv i)⁻¹)
    --   ⦃ Coprod-level Unit-level (Σ-level (op-lvl i) (λ f → Π-level (λ j → Π-level (λ p → W-level op-lvl j )))) ⦄

    W= : {i : I} → W i → W i → Type ℓ
    W= (lf i) (lf .i) = Lift ⊤
    W= (lf i) (nd pw) = Lift ⊥
    W= (nd pw) (lf i) = Lift ⊥
    W= (nd pw) (nd pw') = pw == pw'
    
    postulate

      W=-equiv : {i : I} (w₀ : W i) (w₁ : W i) → (W= w₀ w₁) ≃ (w₀ == w₁)

    -- W-level-aux : ∀ {n} (op-lvl : (i : I) → has-level (S (S n)) (Op P i)) → (i : I) → has-level-aux (S (S n)) (W i)
    -- W-level-aux op-lvl i (lf .i) (lf .i) = equiv-preserves-level (W=-equiv (lf i) (lf i))
    -- W-level-aux op-lvl i (lf .i) (nd pw) = has-level-in (λ p → Empty-rec (lower (<– (W=-equiv (lf i) (nd pw)) p)))
    -- W-level-aux op-lvl i (nd pw) (lf .i) = has-level-in (λ p → Empty-rec (lower (<– (W=-equiv (nd pw) (lf i)) p)))
    -- W-level-aux op-lvl i (nd pw) (nd pw') = equiv-preserves-level (W=-equiv (nd pw) (nd pw'))
    --   ⦃ {!!} ⦄

    -- W-level : ∀ {n} (op-lvl : (i : I) → has-level (S (S n)) (Op P i)) → (i : I) → has-level (S (S n)) (W i)
    -- W-level op-lvl i = has-level-in (W-level-aux op-lvl i)

    
  -- The "slice" of a polynomial by a relator
  _//_ : ∀ {ℓ} {I : Type ℓ} (P : Poly I) (R : Relator P) → Poly (Σ I (Op P))
  Op (P // R) (i , f) = Σ (W P i) (λ w → Σ (Frame P w f) (R w f))
  Param (P // R) (w , α , r) (j , g) = Node P w g
  
  record Domain {ℓ} {I : Type ℓ} (P : Poly I) : Type (lsucc ℓ) where
    coinductive
    field

      R : Relator P 
      D : Domain (P // R)

  open Domain public

  --
  --  Grafting of trees
  --

  module _ {ℓ} {I : Type ℓ} (P : Poly I) where

    Fr : Poly I
    Op Fr = W P
    Param Fr w = Leaf P w

    graft : {i : I} (w : W P i) (ε : ∀ j → Leaf P w j → W P j) → W P i
    graft (lf i) ε = ε i idp
    graft (nd (c , δ)) ε = 
      let ε' j p k l = ε k (j , p , l)
          δ' j p = graft (δ j p) (ε' j p)
      in nd (c , δ')

    --
    --  Leaves in a graft
    --

    graft-leaf-to : {i : I} (w : W P i) (ε : ∀ j → Leaf P w j → W P j) (k : I)
      → Leaf P (graft w ε) k
      → Σ I (λ j → Σ (Leaf P w j) (λ l → Leaf P (ε j l) k))
    graft-leaf-to (lf i) ε k l = i , idp , l
    graft-leaf-to (nd (c , δ)) ε k (j , p , l) = 
      let (s , t , u) = graft-leaf-to (δ j p) (λ k l → ε k (j , p , l)) k l
      in s , (j , p , t) , u

    graft-leaf-from : {i : I} (w : W P i) (ε : ∀ j → Leaf P w j → W P j) (k : I)
      → Σ I (λ j → Σ (Leaf P w j) (λ l → Leaf P (ε j l) k))
      → Leaf P (graft w ε) k
    graft-leaf-from (lf i) ε k (.i , idp , l) = l
    graft-leaf-from (nd (c , δ)) ε k (j₁ , (j₀ , p , l₀) , l₁) = 
      let ε' j p k l = ε k (j , p , l)
          δ' j p = graft (δ j p) (ε' j p)
      in (j₀ , p , graft-leaf-from (δ j₀ p) (ε' j₀ p) k (j₁ , l₀ , l₁))

    abstract
    
      graft-leaf-to-from : {i : I} (w : W P i) (ε : ∀ j → Leaf P w j → W P j) (k : I)
        → (l : Σ I (λ j → Σ (Leaf P w j) (λ l → Leaf P (ε j l) k)))
        → graft-leaf-to w ε k (graft-leaf-from w ε k l) == l
      graft-leaf-to-from (lf i) ε k (.i , idp , l₁) = idp
      graft-leaf-to-from (nd (c , δ)) ε k (j₁ , (j₀ , p , l₀) , l₁) =
        let ε' j p k l = ε k (j , p , l)
            δ' j p = graft (δ j p) (ε' j p)
            (s , t , u) = graft-leaf-to (δ _ p) (ε' _ p) k
                            (graft-leaf-from (δ _ p) (ε' _ p) k (j₁ , l₀ , l₁))
            ih = graft-leaf-to-from (δ j₀ p) (ε' j₀ p) k (j₁ , l₀ , l₁)
        in pair= (fst= ih) (apd↓-cst (λ x → ((j₀ , p , (fst x)) , snd x)) (snd= ih)) 

      graft-leaf-from-to : {i : I} (w : W P i) (ε : ∀ j → Leaf P w j → W P j)
        → (k : I) (l : Leaf P (graft w ε) k)
        → graft-leaf-from w ε k (graft-leaf-to w ε k l) == l
      graft-leaf-from-to (lf i) ε k l = idp
      graft-leaf-from-to (nd (c , δ)) ε k (j , p , l) =
        let ε' j p k l = ε k (j , p , l)
            δ' j p = graft (δ j p) (ε' j p)
        in ap (λ x → (j , p , x)) (graft-leaf-from-to (δ j p) (ε' j p) k l) 

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
      → {j : I} (c : Op P j)
      → Node P w c ⊔ Σ I (λ k → Σ (Leaf P w k) (λ l → Node P (ε k l) c))
      → Node P (graft w ε) c
    graft-node-to (lf i) ε c₀ (inl ())
    graft-node-to (lf i) ε c₀ (inr (.i , idp , n)) = n
    graft-node-to (nd (c , δ)) ε .c (inl (inl idp)) = inl idp
    graft-node-to (nd (c , δ)) ε c₀ (inl (inr (j , p , n))) =
      inr (j , p , graft-node-to (δ j p) (λ k l → ε k (j , p , l)) c₀ (inl n))
    graft-node-to (nd (c , δ)) ε c₀ (inr (k , (j , p , l) , n)) = 
      inr (j , p , graft-node-to (δ j p) (λ k l → ε k (j , p , l)) c₀ (inr (k , l , n)))

    graft-node-from : {i : I} (w : W P i)
      → (ε : ∀ j → Leaf P w j → W P j)
      → {j : I} (c : Op P j)
      → Node P (graft w ε) c
      → Node P w c ⊔ Σ I (λ k → Σ (Leaf P w k) (λ l → Node P (ε k l) c))
    graft-node-from (lf i) ε c₀ n = inr (i , idp , n)
    graft-node-from (nd (c , δ)) ε .c (inl idp) = inl (inl idp)
    graft-node-from (nd (c , δ)) ε c₀ (inr (j , p , n)) with graft-node-from (δ j p) (λ k l → ε k (j , p , l)) c₀ n
    graft-node-from (nd (c , δ)) ε c₀ (inr (j , p , n)) | inl n' = inl (inr (j , p , n'))
    graft-node-from (nd (c , δ)) ε c₀ (inr (j , p , n)) | inr (k , l , n') = inr (k , (j , p , l) , n')

    abstract
    
      graft-node-to-from : {i : I} (w : W P i)
        → (ε : ∀ j → Leaf P w j → W P j)
        → {j : I} (c : Op P j)
        → (n : Node P (graft w ε) c)
        → graft-node-to w ε c (graft-node-from w ε c n) == n
      graft-node-to-from (lf i) ε c₀ n = idp
      graft-node-to-from (nd (c , δ)) ε .c (inl idp) = idp
      graft-node-to-from (nd (c , δ)) ε c₀ (inr (j , p , n)) with
        graft-node-from (δ j p) (λ k l → ε k (j , p , l)) c₀ n |
        inspect (graft-node-from (δ j p) (λ k l → ε k (j , p , l)) c₀) n
      graft-node-to-from (nd (c , δ)) ε c₀ (inr (j , p , n)) | inl n' | ingraph e = 
        ap (λ x → inr (j , p , x)) lem

        where lem = graft-node-to (δ _ p) (λ k l → ε k (j , p , l)) c₀ (inl n')
                      =⟨ ! e |in-ctx (graft-node-to (δ _ p) (λ k l → ε k (j , p , l)) c₀) ⟩
                    graft-node-to (δ _ p) (λ k l → ε k (j , p , l)) c₀
                      (graft-node-from (δ _ p) (λ k l → ε k (j , p , l)) c₀ n)
                      =⟨ graft-node-to-from (δ _ p) (λ k l → ε k (j , p , l)) c₀ n ⟩ 
                    n ∎

      graft-node-to-from (nd (c , δ)) ε c₀ (inr (j , p , n)) | inr (k , l , n') | ingraph e = 
        ap (λ x → inr (j , p , x)) lem

        where lem = graft-node-to (δ _ p) (λ k l → ε k (j , p , l)) c₀ (inr (k , l , n')) 
                      =⟨ ! e |in-ctx (graft-node-to (δ _ p) (λ k l → ε k (j , p , l)) c₀) ⟩
                    graft-node-to (δ _ p) (λ k l → ε k (j , p , l)) c₀
                      (graft-node-from (δ _ p) (λ k l → ε k (j , p , l)) c₀ n)
                      =⟨ graft-node-to-from (δ _ p) (λ k l → ε k (j , p , l)) c₀ n ⟩ 
                    n ∎


      graft-node-from-to : {i : I} (w : W P i)
        → (ε : ∀ j → Leaf P w j → W P j)
        → {j : I} (c : Op P j)
        → (n : Node P w c ⊔ Σ I (λ k → Σ (Leaf P w k) (λ l → Node P (ε k l) c)))
        → graft-node-from w ε c (graft-node-to w ε c n) == n
      graft-node-from-to (lf i) ε c₀ (inl ())
      graft-node-from-to (lf i) ε c₀ (inr (.i , idp , n)) = idp
      graft-node-from-to (nd (c , δ)) ε .c (inl (inl idp)) = idp
      graft-node-from-to (nd (c , δ)) ε c₀ (inl (inr (j , p , n))) with 
        (graft-node-from (δ _ p) (λ k l → ε k (j , p , l)) c₀ ∘ graft-node-to (δ _ p) (λ k l → ε k (j , p , l)) c₀) (inl n)
        | inspect (graft-node-from (δ _ p) (λ k l → ε k (j , p , l)) c₀ ∘ graft-node-to (δ _ p) (λ k l → ε k (j , p , l)) c₀) (inl n)
      graft-node-from-to (nd (c , δ)) ε c₀ (inl (inr (j , p , n))) | inl n' | ingraph e = 
        ap (λ x → inl (inr (j , p , x))) (–> (inl=inl-equiv n' n) lem)

        where lem = inl n' =⟨ ! e ⟩
                    graft-node-from (δ _ p) (λ k l → ε k (j , p , l)) c₀
                      (graft-node-to (δ _ p) (λ k l → ε k (j , p , l)) c₀ (inl n))
                      =⟨ graft-node-from-to (δ _ p) (λ k l → ε k (j , p , l)) c₀ (inl n) ⟩ 
                    inl n ∎

      graft-node-from-to (nd (c , δ)) ε c₀ (inl (inr (j , p , n))) | inr (k , l , n') | ingraph e = 
        ⊥-elim (inr≠inl (k , l , n') n lem)

        where lem = inr (k , l , n') =⟨ ! e ⟩
                    graft-node-from (δ _ p) (λ k₁ l₁ → ε k₁ (j , p , l₁)) c₀
                      (graft-node-to (δ _ p) (λ k₁ l₁ → ε k₁ (j , p , l₁)) c₀ (inl n))
                      =⟨ graft-node-from-to (δ _ p) (λ k l → ε k (j , p , l)) c₀ (inl n) ⟩ 
                    inl n ∎

      graft-node-from-to (nd (c , δ)) ε c₀ (inr (k , (j , p , l) , n)) with
        (graft-node-from (δ _ p) (λ k l → ε k (j , p , l)) c₀ ∘ graft-node-to (δ _ p) (λ k l → ε k (j , p , l)) c₀) (inr (k , l , n))
        | inspect (graft-node-from (δ _ p) (λ k l → ε k (j , p , l)) c₀ ∘ graft-node-to (δ _ p) (λ k l → ε k (j , p , l)) c₀) (inr (k , l , n))
      graft-node-from-to (nd (c , δ)) ε c₀ (inr (k , (j , p , l) , n)) | inl n' | ingraph e = 
        ⊥-elim (inl≠inr n' (k , l , n) lem)

        where lem = inl n' =⟨ ! e ⟩
                    graft-node-from (δ _ p) (λ k l → ε k (j , p , l)) c₀
                      (graft-node-to (δ _ p) (λ k l → ε k (j , p , l)) c₀ (inr (k , l , n)))
                      =⟨ graft-node-from-to (δ _ p) (λ k l → ε k (j , p , l)) c₀ (inr (k , l , n)) ⟩
                    inr (k , l , n) ∎

      graft-node-from-to (nd (c , δ)) ε c₀ (inr (k , (j , p , l) , n)) | inr (k' , l' , n') | ingraph e = 
        let lem' = –> (inr=inr-equiv (k' , l' , n') (k , l , n)) lem
        in ap inr (pair= (fst= lem') (apd↓-cst (λ x → ((j , p , fst x) , snd x)) (snd= lem')))

        where lem = inr (k' , l' , n') =⟨ ! e ⟩ 
                    graft-node-from (δ _ p) (λ k l → ε k (j , p , l)) c₀
                      (graft-node-to (δ _ p) (λ k l → ε k (j , p , l)) c₀ (inr (k , l , n)))
                      =⟨ graft-node-from-to (δ _ p) (λ k l → ε k (j , p , l)) c₀ (inr (k , l , n)) ⟩ 
                    inr (k , l , n) ∎
      
    graft-node-eqv : {i : I} (w : W P i)
      → (ε : ∀ j → Leaf P w j → W P j)
      → {j : I} (c : Op P j)
      → Node P w c ⊔ Σ I (λ k → Σ (Leaf P w k) (λ l → Node P (ε k l) c))
        ≃ Node P (graft w ε) c
    graft-node-eqv w ε c =
      equiv (graft-node-to w ε c) (graft-node-from w ε c)
            (graft-node-to-from w ε c) (graft-node-from-to w ε c)






