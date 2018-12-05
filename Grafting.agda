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
    → Leaf P (graft w ψ) k
    → Σ I (λ j → Σ (Leaf P w j) (λ l → Leaf P (ψ j l) k))
  graft-leaf-to (lf i) ψ k l = i , idp , l
  graft-leaf-to (nd (f ,  ϕ)) ψ k (j , p , l) = 
    let (s , t , u) = graft-leaf-to (ϕ j p) (λ k l → ψ k (j , p , l)) k l
    in s , (j , p , t) , u

  graft-leaf-from : {i : I} (w : W P i) (ψ : ∀ j → Leaf P w j → W P j) (k : I)
    → Σ I (λ j → Σ (Leaf P w j) (λ l → Leaf P (ψ j l) k))
    → Leaf P (graft w ψ) k
  graft-leaf-from (lf i) ψ k (.i , idp , l) = l
  graft-leaf-from (nd (f ,  ϕ)) ψ k (j₁ , (j₀ , p , l₀) , l₁) = 
    let ψ' j p k l = ψ k (j , p , l)
        ϕ' j p = graft (ϕ j p) (ψ' j p)
    in (j₀ , p , graft-leaf-from (ϕ j₀ p) (ψ' j₀ p) k (j₁ , l₀ , l₁))

  abstract

    graft-leaf-to-from : {i : I} (w : W P i) (ψ : ∀ j → Leaf P w j → W P j) (k : I)
      → (l : Σ I (λ j → Σ (Leaf P w j) (λ l → Leaf P (ψ j l) k)))
      → graft-leaf-to w ψ k (graft-leaf-from w ψ k l) == l
    graft-leaf-to-from (lf i) ψ k (.i , idp , l₁) = idp
    graft-leaf-to-from (nd (f ,  ϕ)) ψ k (j₁ , (j₀ , p , l₀) , l₁) =
      let ψ' j p k l = ψ k (j , p , l)
          ϕ' j p = graft (ϕ j p) (ψ' j p)
          (s , t , u) = graft-leaf-to (ϕ _ p) (ψ' _ p) k
                          (graft-leaf-from (ϕ _ p) (ψ' _ p) k (j₁ , l₀ , l₁))
          ih = graft-leaf-to-from (ϕ j₀ p) (ψ' j₀ p) k (j₁ , l₀ , l₁)
      in pair= (fst= ih) (apd↓-cst (λ x → ((j₀ , p , (fst x)) , snd x)) (snd= ih)) 

    graft-leaf-from-to : {i : I} (w : W P i) (ψ : ∀ j → Leaf P w j → W P j)
      → (k : I) (l : Leaf P (graft w ψ) k)
      → graft-leaf-from w ψ k (graft-leaf-to w ψ k l) == l
    graft-leaf-from-to (lf i) ψ k l = idp
    graft-leaf-from-to (nd (f ,  ϕ)) ψ k (j , p , l) =
      let ψ' j p k l = ψ k (j , p , l)
          ϕ' j p = graft (ϕ j p) (ψ' j p)
      in ap (λ x → (j , p , x)) (graft-leaf-from-to (ϕ j p) (ψ' j p) k l) 

  graft-leaf-eqv : {i : I} (w : W P i) (ψ : ∀ j → Leaf P w j → W P j) (k : I)
    → Leaf P (graft w ψ) k
      ≃ Σ I (λ j → Σ (Leaf P w j) (λ l → Leaf P (ψ j l) k))
  graft-leaf-eqv w ψ k =
    equiv (graft-leaf-to w ψ k) (graft-leaf-from w ψ k)
          (graft-leaf-to-from w ψ k) (graft-leaf-from-to w ψ k)

  --
  --  Nodes in a graft
  --

  graft-node-to : {i : I} (w : W P i)
    → (ψ : ∀ j → Leaf P w j → W P j)
    → (g : Ops P)
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
    → (ψ : ∀ j → Leaf P w j → W P j)
    → (g : Ops P)
    → Node P (graft w ψ) g
    → Node P w g ⊔ Σ I (λ k → Σ (Leaf P w k) (λ l → Node P (ψ k l) g))
  graft-node-from (lf i) ψ g n = inr (i , idp , n)
  graft-node-from (nd (f ,  ϕ)) ψ ._ (inl idp) = inl (inl idp)
  graft-node-from (nd (f ,  ϕ)) ψ g (inr (j , p , n)) with graft-node-from (ϕ j p) (λ k l → ψ k (j , p , l)) g n
  graft-node-from (nd (f ,  ϕ)) ψ g (inr (j , p , n)) | inl n' = inl (inr (j , p , n'))
  graft-node-from (nd (f ,  ϕ)) ψ g (inr (j , p , n)) | inr (k , l , n') = inr (k , (j , p , l) , n')


  abstract

    graft-node-to-from : {i : I} (w : W P i)
      → (ψ : ∀ j → Leaf P w j → W P j)
      → (g : Ops P)
      → (n : Node P (graft w ψ) g)
      → graft-node-to w ψ g (graft-node-from w ψ g n) == n
    graft-node-to-from (lf i) ψ g n = idp
    graft-node-to-from (nd (f ,  ϕ)) ψ ._ (inl idp) = idp
    graft-node-to-from (nd (f ,  ϕ)) ψ g (inr (j , p , n)) with
      graft-node-from (ϕ j p) (λ k l → ψ k (j , p , l)) g n |
      inspect (graft-node-from (ϕ j p) (λ k l → ψ k (j , p , l)) g) n
    graft-node-to-from (nd (f ,  ϕ)) ψ g (inr (j , p , n)) | inl n' | ingraph e = 
      ap (λ x → inr (j , p , x)) lem

      where lem = graft-node-to (ϕ _ p) (λ k l → ψ k (j , p , l)) g (inl n')
                    =⟨ ! e |in-ctx (graft-node-to (ϕ _ p) (λ k l → ψ k (j , p , l)) g) ⟩
                  graft-node-to (ϕ _ p) (λ k l → ψ k (j , p , l)) g
                    (graft-node-from (ϕ _ p) (λ k l → ψ k (j , p , l)) g n)
                    =⟨ graft-node-to-from (ϕ _ p) (λ k l → ψ k (j , p , l)) g n ⟩ 
                  n ∎

    graft-node-to-from (nd (f ,  ϕ)) ψ g (inr (j , p , n)) | inr (k , l , n') | ingraph e = 
      ap (λ x → inr (j , p , x)) lem

      where lem = graft-node-to (ϕ _ p) (λ k l → ψ k (j , p , l)) g (inr (k , l , n')) 
                    =⟨ ! e |in-ctx (graft-node-to (ϕ _ p) (λ k l → ψ k (j , p , l)) g) ⟩
                  graft-node-to (ϕ _ p) (λ k l → ψ k (j , p , l)) g
                    (graft-node-from (ϕ _ p) (λ k l → ψ k (j , p , l)) g n)
                    =⟨ graft-node-to-from (ϕ _ p) (λ k l → ψ k (j , p , l)) g n ⟩ 
                  n ∎


    graft-node-from-to : {i : I} (w : W P i)
      → (ψ : ∀ j → Leaf P w j → W P j)
      → (g : Ops P)
      → (n : Node P w g ⊔ Σ I (λ k → Σ (Leaf P w k) (λ l → Node P (ψ k l) g)))
      → graft-node-from w ψ g (graft-node-to w ψ g n) == n
    graft-node-from-to (lf i) ψ g (inl ())
    graft-node-from-to (lf i) ψ g (inr (.i , idp , n)) = idp
    graft-node-from-to (nd (f ,  ϕ)) ψ ._ (inl (inl idp)) = idp
    graft-node-from-to (nd (f ,  ϕ)) ψ g (inl (inr (j , p , n))) with 
      (graft-node-from (ϕ _ p) (λ k l → ψ k (j , p , l)) g ∘ graft-node-to (ϕ _ p) (λ k l → ψ k (j , p , l)) g) (inl n)
      | inspect (graft-node-from (ϕ _ p) (λ k l → ψ k (j , p , l)) g ∘ graft-node-to (ϕ _ p) (λ k l → ψ k (j , p , l)) g) (inl n)
    graft-node-from-to (nd (f ,  ϕ)) ψ g (inl (inr (j , p , n))) | inl n' | ingraph e = 
      ap (λ x → inl (inr (j , p , x))) (–> (inl=inl-equiv n' n) lem)

      where lem = inl n' =⟨ ! e ⟩
                  graft-node-from (ϕ _ p) (λ k l → ψ k (j , p , l)) g
                    (graft-node-to (ϕ _ p) (λ k l → ψ k (j , p , l)) g (inl n))
                    =⟨ graft-node-from-to (ϕ _ p) (λ k l → ψ k (j , p , l)) g (inl n) ⟩ 
                  inl n ∎

    graft-node-from-to (nd (f ,  ϕ)) ψ g (inl (inr (j , p , n))) | inr (k , l , n') | ingraph e = 
      ⊥-elim (inr≠inl (k , l , n') n lem)

      where lem = inr (k , l , n') =⟨ ! e ⟩
                  graft-node-from (ϕ _ p) (λ k₁ l₁ → ψ k₁ (j , p , l₁)) g
                    (graft-node-to (ϕ _ p) (λ k₁ l₁ → ψ k₁ (j , p , l₁)) g (inl n))
                    =⟨ graft-node-from-to (ϕ _ p) (λ k l → ψ k (j , p , l)) g (inl n) ⟩ 
                  inl n ∎

    graft-node-from-to (nd (f ,  ϕ)) ψ g (inr (k , (j , p , l) , n)) with
      (graft-node-from (ϕ _ p) (λ k l → ψ k (j , p , l)) g ∘ graft-node-to (ϕ _ p) (λ k l → ψ k (j , p , l)) g) (inr (k , l , n))
      | inspect (graft-node-from (ϕ _ p) (λ k l → ψ k (j , p , l)) g ∘ graft-node-to (ϕ _ p) (λ k l → ψ k (j , p , l)) g) (inr (k , l , n))
    graft-node-from-to (nd (f ,  ϕ)) ψ g (inr (k , (j , p , l) , n)) | inl n' | ingraph e = 
      ⊥-elim (inl≠inr n' (k , l , n) lem)

      where lem = inl n' =⟨ ! e ⟩
                  graft-node-from (ϕ _ p) (λ k l → ψ k (j , p , l)) g
                    (graft-node-to (ϕ _ p) (λ k l → ψ k (j , p , l)) g (inr (k , l , n)))
                    =⟨ graft-node-from-to (ϕ _ p) (λ k l → ψ k (j , p , l)) g (inr (k , l , n)) ⟩
                  inr (k , l , n) ∎

    graft-node-from-to (nd (f ,  ϕ)) ψ g (inr (k , (j , p , l) , n)) | inr (k' , l' , n') | ingraph e = 
      let lem' = –> (inr=inr-equiv (k' , l' , n') (k , l , n)) lem
      in ap inr (pair= (fst= lem') (apd↓-cst (λ x → ((j , p , fst x) , snd x)) (snd= lem')))

      where lem = inr (k' , l' , n') =⟨ ! e ⟩ 
                  graft-node-from (ϕ _ p) (λ k l → ψ k (j , p , l)) g
                    (graft-node-to (ϕ _ p) (λ k l → ψ k (j , p , l)) g (inr (k , l , n)))
                    =⟨ graft-node-from-to (ϕ _ p) (λ k l → ψ k (j , p , l)) g (inr (k , l , n)) ⟩ 
                  inr (k , l , n) ∎

  graft-node-eqv : {i : I} (w : W P i)
    → (ψ : ∀ j → Leaf P w j → W P j)
    → (g : Ops P)
    → Node P w g ⊔ Σ I (λ k → Σ (Leaf P w k) (λ l → Node P (ψ k l) g))
      ≃ Node P (graft w ψ) g
  graft-node-eqv w ψ g =
    equiv (graft-node-to w ψ g) (graft-node-from w ψ g)
          (graft-node-to-from w ψ g) (graft-node-from-to w ψ g)


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
    → (ψ₁ : ∀ k → (t : Σ I (λ j → Σ (Leaf P w j) (λ l → Leaf P (ψ₀ j l) k))) → W P k)
    → graft (graft w ψ₀) (λ j l → ψ₁ j (graft-leaf-to w ψ₀ j l)) ==
      graft w (λ j l₀ → graft (ψ₀ j l₀) (λ k l₁ → ψ₁ k (j , l₀ , l₁)))
  graft-assoc (lf i) ψ₀ ψ₁ = idp
  graft-assoc (nd (f , ϕ)) ψ₀ ψ₁ = ap (λ x → nd (f , x))
    (λ= (λ j → λ= (λ p → graft-assoc (ϕ j p) (λ k l → ψ₀ k (j , p , l))
      (λ k t → ψ₁ k (fst t , (j , p , fst (snd t)) , snd (snd t))))))


