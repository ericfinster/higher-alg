{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Grafting

--
--  The postulates in this file are not really postulates.  In each
--  case, the equivalence in question can be written as the composite
--  of more primitive equivalences.  However, writing it in this way
--  causes serious performance issues with Agda's typechecker later
--  on.  As such, I have written out the forward and backward
--  functions but not bothered to expand out the proofs that they are
--  mutually inverse, as we would make these proofs abstract in any
--  case.
--

module Substitution {ℓ} {I : Type ℓ} (P : Poly I) where

  -- Elementary substitution.
  subst : {i : I} (w : W P i)
    → (κ : (g : Ops P) → Node P w g → InFrame P g)
    → W P i
  subst (lf i) κ = lf i
  subst (nd (f , ϕ)) κ =
    let (w , α) = κ (_ , f) (inl idp)
        κ' j l g n = κ g (inr (j , –> (α j) l , n))
        ψ j l = subst (ϕ j (–> (α j) l)) (κ' j l)
    in graft P w ψ

  -- Leaves in a substitution

  subst-lf-to : {i : I} (w : W P i)
    → (κ : (g : Ops P) → Node P w g → InFrame P g)
    → (j : I) → Leaf P w j → Leaf P (subst w κ) j 
  subst-lf-to (lf i) κ j l = l
  subst-lf-to (nd (f , ϕ)) κ j (k , p , l) = 
    let (w , α) = κ (_ , f) (inl idp)
        κ' j l g n = κ g (inr (j , –> (α j) l , n))
        ψ j l = subst (ϕ j (–> (α j) l)) (κ' j l)
        l' = subst-lf-to (ϕ k p) (λ g n → κ g (inr (k , p , n))) j l
        Q x = Leaf P (subst (ϕ k x) (λ g n → κ g (inr (k , x , n)))) j
    in graft-leaf-to P w ψ j (k , <– (α k) p , transport! Q (<–-inv-r (α k) p) l')

  subst-lf-from : {i : I} (w : W P i)
    → (κ : (g : Ops P) → Node P w g → InFrame P g)
    → (j : I) → Leaf P (subst w κ) j → Leaf P w j
  subst-lf-from (lf i) κ j l = l
  subst-lf-from (nd (f , ϕ)) κ j l = 
    let (w , α) = κ (_ , f) (inl idp)
        κ' j l g n = κ g (inr (j , –> (α j) l , n))
        ψ j l = subst (ϕ j (–> (α j) l)) (κ' j l)
        (k , l₀ , l₁) = graft-leaf-from P w ψ j l
    in k , –> (α k) l₀ , subst-lf-from (ϕ k (–> (α k) l₀)) (κ' k l₀) j l₁

  postulate

    subst-lf-to-from : {i : I} (w : W P i)
      → (κ : (g : Ops P) → Node P w g → InFrame P g)
      → (j : I) (l : Leaf P (subst w κ) j)
      → subst-lf-to w κ j (subst-lf-from w κ j l) == l

    subst-lf-from-to : {i : I} (w : W P i)
      → (κ : (g : Ops P) → Node P w g → InFrame P g)
      → (j : I) (l : Leaf P w j)
      → subst-lf-from w κ j (subst-lf-to w κ j l) == l

  subst-lf-eqv : {i : I} (w : W P i)
    → (κ : (g : Ops P) → Node P w g → InFrame P g)
    → (j : I) → Leaf P w j ≃ Leaf P (subst w κ) j 
  subst-lf-eqv w κ j = equiv (subst-lf-to w κ j) (subst-lf-from w κ j)
    (subst-lf-to-from w κ j) (subst-lf-from-to w κ j)

  -- Nodes in a substitution
  subst-nd-to : {i : I} (w : W P i)
    → (κ : (g : Ops P) → Node P w g → InFrame P g)
    → (g : Ops P) → Σ (Ops P) (λ h → Σ (Node P w h) (λ n → Node P (fst (κ h n)) g))
    → Node P (subst w κ) g
  subst-nd-to (lf i) κ g (h , lift () , n₁)
  subst-nd-to (nd (f , ϕ)) κ g (._ , inl idp , n₁) = 
    let (w , α) = κ (_ , f) (inl idp)
        κ' j l g n = κ g (inr (j , –> (α j) l , n))
        ψ j l = subst (ϕ j (–> (α j) l)) (κ' j l)
    in graft-node-to P w ψ g (inl n₁)
  subst-nd-to (nd (f , ϕ)) κ g (h , inr (k , p , n₀) , n₁) = 
    let (w , α) = κ (_ , f) (inl idp)
        κ' j l g n = κ g (inr (j , –> (α j) l , n))
        ψ j l = subst (ϕ j (–> (α j) l)) (κ' j l)
        n' = subst-nd-to (ϕ k p) (λ g n → κ g (inr (k , p , n))) g (h , n₀ , n₁)
        Q x = Node P (subst (ϕ k x) (λ g n → κ g (inr (k , x , n)))) g
    in graft-node-to P w ψ g (inr (k , <– (α k) p , transport! Q (<–-inv-r (α k) p) n'))

  subst-nd-from : {i : I} (w : W P i)
    → (κ : (g : Ops P) → Node P w g → InFrame P g)
    → (g : Ops P) → Node P (subst w κ) g
    → Σ (Ops P) (λ h → Σ (Node P w h) (λ n → Node P (fst (κ h n)) g))

  subst-nd-from-lcl : {i : I} (f : Op P i)
    → (ϕ : (j : I) → Param P f j → W P j) 
    → (κ : (h : Ops P) → Node P (nd (f , ϕ)) h → InFrame P h) (g : Ops P)
    → (n : let (w , α) = κ (_ , f) (inl idp)
               κ' j l h n = κ h (inr (j , –> (α j) l , n))
               ψ j l = subst (ϕ j (–> (α j) l)) (κ' j l)
           in Node P w g ⊔ Σ I (λ j → Σ (Leaf P w j) (λ l → Node P (ψ j l) g)))
    → Σ (Ops P) (λ h → Σ (Node P (nd (f , ϕ)) h) (λ n' → Node P (fst (κ h n')) g))

  subst-nd-from (lf i) κ g (lift ())
  subst-nd-from (nd (f , ϕ)) κ g n = 
    let (w , α) = κ (_ , f) (inl idp)
        κ' j l g n = κ g (inr (j , –> (α j) l , n))
        ψ j l = subst (ϕ j (–> (α j) l)) (κ' j l)
    in  subst-nd-from-lcl f ϕ κ g (graft-node-from P w ψ g n) 

  subst-nd-from-lcl f ϕ κ g (inl n) = (_ , f) , inl idp , n
  subst-nd-from-lcl f ϕ κ g (inr (j , l , n)) =
    let (w , α) = κ (_ , f) (inl idp)
        κ' j l g n = κ g (inr (j , –> (α j) l , n))
        ψ j l = subst (ϕ j (–> (α j) l)) (κ' j l)
        (h , n₀ , n₁) = subst-nd-from (ϕ j (–> (α j) l)) (κ' j l) g n
    in h , inr (j , –> (α j) l , n₀) , n₁

  postulate

    subst-nd-to-from : {i : I} (w : W P i)
      → (κ : (g : Ops P) → Node P w g → InFrame P g)
      → (g : Ops P) (n : Node P (subst w κ) g)
      → subst-nd-to w κ g (subst-nd-from w κ g n) == n
      
    subst-nd-from-to : {i : I} (w : W P i)
      → (κ : (g : Ops P) → Node P w g → InFrame P g)
      → (g : Ops P) (n : Σ (Ops P) (λ h → Σ (Node P w h) (λ n → Node P (fst (κ h n)) g)))
      → subst-nd-from w κ g (subst-nd-to w κ g n) == n

  subst-nd-eqv : {i : I} (w : W P i)
    → (κ : (g : Ops P) → Node P w g → InFrame P g) (g : Ops P)
    → Σ (Ops P) (λ h → Σ (Node P w h) (λ n → Node P (fst (κ h n)) g))
    ≃ Node P (subst w κ) g 
  subst-nd-eqv w κ g = equiv (subst-nd-to w κ g) (subst-nd-from w κ g)
    (subst-nd-to-from w κ g) (subst-nd-from-to w κ g)

