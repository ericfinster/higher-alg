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

  -- The "slice" of a polynomial by a relator
  _//_ : {I : Type₀} (P : Poly I) (R : Relator P) → Poly (Σ I (Op P))
  Op (P // R) (i , f) = Σ (W P i) (λ w → Σ (Frame P w f) (R w f))
  Param (P // R) (w , α , r) (j , g) = Node P w g
  
  record Domain {I : Type₀} (P : Poly I) : Type₁ where
    coinductive
    field

      R : Relator P 
      D : Domain (P // R)

  open Domain public

  --
  --  Grafting of trees
  --

  module _ {I : Type₀} (P : Poly I) where

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
      in (j₀ , p , graft-leaf-from (δ _ p) (ε' _ p) k (j₁ , l₀ , l₁))

    -- abstract
    
    --   graft-leaf-to-from : {i : I} (w : W P i) (ε : ∀ j → Leaf P w j → W P j) (k : I)
    --     → (l : Σ I (λ j → Σ (Leaf P w j) (λ l → Leaf P (ε j l) k)))
    --     → graft-leaf-to w ε k (graft-leaf-from w ε k l) == l
    --   graft-leaf-to-from (lf i) ε k (.i , leaf .i , l₁) = idp
    --   graft-leaf-to-from (nd (c , δ)) ε k (j , stem p l₀ , l₁) =
    --     let ε' j p k l = ε k (stem p l)
    --         δ' j p = graft (δ j p) (ε' j p)
    --         (s , t , u) = graft-leaf-to (δ _ p) (ε' _ p) k
    --                         (graft-leaf-from (δ _ p) (ε' _ p) k (j , l₀ , l₁))
    --         ih = graft-leaf-to-from (δ _ p) (ε' _ p) k (j , l₀ , l₁)
    --     in pair= (fst= ih) (apd↓-cst (λ x → (stem p (fst x) , snd x)) (snd= ih)) 

    --   graft-leaf-from-to : {i : I} (w : W P i) (ε : ∀ j → Leaf P w j → W P j)
    --     → (k : I) (l : Leaf P (graft w ε) k)
    --     → graft-leaf-from w ε k (graft-leaf-to w ε k l) == l
    --   graft-leaf-from-to (lf i) ε k l = idp
    --   graft-leaf-from-to (nd (c , δ)) ε k (stem p l) =
    --     let ε' j p k l = ε k (stem p l)
    --         δ' j p = graft (δ j p) (ε' j p)
    --     in ap (λ x → stem p x) (graft-leaf-from-to (δ _ p) (ε' _ p) k l) 

    -- graft-leaf-eqv : {i : I} (w : W P i) (ε : ∀ j → Leaf P w j → W P j) (k : I)
    --   → Leaf P (graft w ε) k
    --     ≃ Σ I (λ j → Σ (Leaf P w j) (λ l → Leaf P (ε j l) k))
    -- graft-leaf-eqv w ε k =
    --   equiv (graft-leaf-to w ε k) (graft-leaf-from w ε k)
    --         (graft-leaf-to-from w ε k) (graft-leaf-from-to w ε k)

    -- --
    -- --  Nodes in a graft
    -- --

    -- graft-node-to : {i : I} (w : W P i)
    --   → (ε : ∀ j → Leaf P w j → W P j)
    --   → {j : I} (c : γ P j)
    --   → Node P w c ⊔ Σ I (λ k → Σ (Leaf P w k) (λ l → Node P (ε k l) c))
    --   → Node P (graft w ε) c
    -- graft-node-to (lf i) ε c₀ (inl ())
    -- graft-node-to (lf i) ε c₀ (inr (.i , leaf .i , n)) = n
    -- graft-node-to (nd (c , δ)) ε .c (inl this) = this
    -- graft-node-to (nd (c , δ)) ε c₀ (inl (that p n)) =
    --   that p (graft-node-to (δ _ p) (λ k l → ε k (stem p l)) c₀ (inl n))
    -- graft-node-to (nd (c , δ)) ε c₀ (inr (k , stem p l , n)) = 
    --   that p (graft-node-to (δ _ p) (λ k l → ε k (stem p l)) c₀ (inr (k , l , n)))

    -- graft-node-from : {i : I} (w : W P i)
    --   → (ε : ∀ j → Leaf P w j → W P j)
    --   → {j : I} (c : γ P j)
    --   → Node P (graft w ε) c
    --   → Node P w c ⊔ Σ I (λ k → Σ (Leaf P w k) (λ l → Node P (ε k l) c))
    -- graft-node-from (lf i) ε c₀ n = inr (i , leaf i , n)
    -- graft-node-from (nd (c , δ)) ε .c this = inl this
    -- graft-node-from (nd (c , δ)) ε c₀ (that p n) with graft-node-from (δ _ p) (λ k l → ε k (stem p l)) c₀ n
    -- graft-node-from (nd (c , δ)) ε c₀ (that p n) | inl n' = inl (that p n')
    -- graft-node-from (nd (c , δ)) ε c₀ (that p n) | inr (k , l , n') = inr (k , stem p l , n')

    -- abstract
    
    --   graft-node-to-from : {i : I} (w : W P i)
    --     → (ε : ∀ j → Leaf P w j → W P j)
    --     → {j : I} (c : γ P j)
    --     → (n : Node P (graft w ε) c)
    --     → graft-node-to w ε c (graft-node-from w ε c n) == n
    --   graft-node-to-from (lf i) ε c₀ n = idp
    --   graft-node-to-from (nd (c , δ)) ε .c this = idp
    --   graft-node-to-from (nd (c , δ)) ε c₀ (that p n) with
    --     graft-node-from (δ _ p) (λ k l → ε k (stem p l)) c₀ n |
    --     inspect (graft-node-from (δ _ p) (λ k l → ε k (stem p l)) c₀) n
    --   graft-node-to-from (nd (c , δ)) ε c₀ (that p n) | inl n' | ingraph e =
    --     ap (that p) lem

    --     where lem = graft-node-to (δ _ p) (λ k l → ε k (stem p l)) c₀ (inl n')
    --                   =⟨ ! e |in-ctx (graft-node-to (δ _ p) (λ k l → ε k (stem p l)) c₀) ⟩
    --                 graft-node-to (δ _ p) (λ k l → ε k (stem p l)) c₀
    --                   (graft-node-from (δ _ p) (λ k l → ε k (stem p l)) c₀ n)
    --                   =⟨ graft-node-to-from (δ _ p) (λ k l → ε k (stem p l)) c₀ n ⟩ 
    --                 n ∎

    --   graft-node-to-from (nd (c , δ)) ε c₀ (that p n) | inr (k , l , n') | ingraph e =
    --     ap (that p) lem

    --     where lem = graft-node-to (δ _ p) (λ k l → ε k (stem p l)) c₀ (inr (k , l , n')) 
    --                   =⟨ ! e |in-ctx (graft-node-to (δ _ p) (λ k l → ε k (stem p l)) c₀) ⟩
    --                 graft-node-to (δ _ p) (λ k l → ε k (stem p l)) c₀
    --                   (graft-node-from (δ _ p) (λ k l → ε k (stem p l)) c₀ n)
    --                   =⟨ graft-node-to-from (δ _ p) (λ k l → ε k (stem p l)) c₀ n ⟩ 
    --                 n ∎


    --   graft-node-from-to : {i : I} (w : W P i)
    --     → (ε : ∀ j → Leaf P w j → W P j)
    --     → {j : I} (c : γ P j)
    --     → (n : Node P w c ⊔ Σ I (λ k → Σ (Leaf P w k) (λ l → Node P (ε k l) c)))
    --     → graft-node-from w ε c (graft-node-to w ε c n) == n
    --   graft-node-from-to (lf i) ε c₀ (inl ())
    --   graft-node-from-to (lf i) ε c₀ (inr (.i , leaf .i , n)) = idp
    --   graft-node-from-to (nd (c , δ)) ε .c (inl this) = idp
    --   graft-node-from-to (nd (c , δ)) ε c₀ (inl (that p n)) with 
    --     (graft-node-from (δ _ p) (λ k l → ε k (stem p l)) c₀ ∘ graft-node-to (δ _ p) (λ k l → ε k (stem p l)) c₀) (inl n)
    --     | inspect (graft-node-from (δ _ p) (λ k l → ε k (stem p l)) c₀ ∘ graft-node-to (δ _ p) (λ k l → ε k (stem p l)) c₀) (inl n)
    --   graft-node-from-to (nd (c , δ)) ε c₀ (inl (that p n)) | inl n' | ingraph e =
    --     ap (λ x → inl (that p x)) (–> (inl=inl-equiv n' n) lem)

    --     where lem = inl n' =⟨ ! e ⟩
    --                 graft-node-from (δ _ p) (λ k l → ε k (stem p l)) c₀
    --                   (graft-node-to (δ _ p) (λ k l → ε k (stem p l)) c₀ (inl n))
    --                   =⟨ graft-node-from-to (δ _ p) (λ k l → ε k (stem p l)) c₀ (inl n) ⟩ 
    --                 inl n ∎

    --   graft-node-from-to (nd (c , δ)) ε c₀ (inl (that p n)) | inr (k , l , n') | ingraph e =
    --     ⊥-elim (inr≠inl (k , l , n') n lem)

    --     where lem = inr (k , l , n') =⟨ ! e ⟩
    --                 graft-node-from (δ _ p) (λ k₁ l₁ → ε k₁ (stem p l₁)) c₀
    --                   (graft-node-to (δ _ p) (λ k₁ l₁ → ε k₁ (stem p l₁)) c₀ (inl n))
    --                   =⟨ graft-node-from-to (δ _ p) (λ k l → ε k (stem p l)) c₀ (inl n) ⟩ 
    --                 inl n ∎

    --   graft-node-from-to (nd (c , δ)) ε c₀ (inr (k , stem p l , n)) with
    --     (graft-node-from (δ _ p) (λ k l → ε k (stem p l)) c₀ ∘ graft-node-to (δ _ p) (λ k l → ε k (stem p l)) c₀) (inr (k , l , n))
    --     | inspect (graft-node-from (δ _ p) (λ k l → ε k (stem p l)) c₀ ∘ graft-node-to (δ _ p) (λ k l → ε k (stem p l)) c₀) (inr (k , l , n))
    --   graft-node-from-to (nd (c , δ)) ε c₀ (inr (k , stem p l , n)) | inl n' | ingraph e =
    --     ⊥-elim (inl≠inr n' (k , l , n) lem)

    --     where lem = inl n' =⟨ ! e ⟩
    --                 graft-node-from (δ _ p) (λ k l → ε k (stem p l)) c₀
    --                   (graft-node-to (δ _ p) (λ k l → ε k (stem p l)) c₀ (inr (k , l , n)))
    --                   =⟨ graft-node-from-to (δ _ p) (λ k l → ε k (stem p l)) c₀ (inr (k , l , n)) ⟩
    --                 inr (k , l , n) ∎

    --   graft-node-from-to (nd (c , δ)) ε c₀ (inr (k , stem p l , n)) | inr (k' , l' , n') | ingraph e =
    --     let lem' = –> (inr=inr-equiv (k' , l' , n') (k , l , n)) lem
    --     in ap inr (pair= (fst= lem') (apd↓-cst (λ x → (stem p (fst x) , snd x)) (snd= lem')))

    --     where lem = inr (k' , l' , n') =⟨ ! e ⟩ 
    --                 graft-node-from (δ _ p) (λ k l → ε k (stem p l)) c₀
    --                   (graft-node-to (δ _ p) (λ k l → ε k (stem p l)) c₀ (inr (k , l , n)))
    --                   =⟨ graft-node-from-to (δ _ p) (λ k l → ε k (stem p l)) c₀ (inr (k , l , n)) ⟩ 
    --                 inr (k , l , n) ∎
      
    -- graft-node-eqv : {i : I} (w : W P i)
    --   → (ε : ∀ j → Leaf P w j → W P j)
    --   → {j : I} (c : γ P j)
    --   → Node P w c ⊔ Σ I (λ k → Σ (Leaf P w k) (λ l → Node P (ε k l) c))
    --     ≃ Node P (graft w ε) c
    -- graft-node-eqv w ε c =
    --   equiv (graft-node-to w ε c) (graft-node-from w ε c)
    --         (graft-node-to-from w ε c) (graft-node-from-to w ε c)






