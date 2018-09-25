{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Substitution

module Indexed where

  module _ {ℓ} {I : Type ℓ} (P : Poly I) where
    
    data Sort : ℕ → Type ℓ
    data Oper : (n : ℕ) → Sort n → Type ℓ
    data Tr : (n : ℕ) → Sort n → Type ℓ

    Params : (n : ℕ) {i : Sort n} (f : Oper n i) → Type ℓ
    Leaves : (n : ℕ) {i : Sort n} (w : Tr n i) → Type ℓ

    τₚ : (n : ℕ) {i : Sort n} {f : Oper n i} (p : Params n f) → Sort n
    τₗ : (n : ℕ) {i : Sort n} {w : Tr n i} (l : Leaves n w) → Sort n
    
    Frm : (n : ℕ) {i : Sort n} (w : Tr n i) (f : Oper n i) → Type ℓ
    Frm n w f = Σ (Leaves n w ≃ Params n f) (λ α → (l : Leaves n w) → τₗ n l == τₚ n (–> α l))

    data Sort where
      idx : (i : I) → Sort 0
      _,_ : {n : ℕ} → (i : Sort n) → Oper n i → Sort (S n)
      
    -- The hypothetical multiplication in positive dimensions
    μ∞ : (n : ℕ) {i : Sort n} {f : Oper n i} 
      → Tr (S n) (i , f) → Oper (S n) (i , f)

    -- The dimension indexing here, however, seems somewhat strange ...
    
    data Oper where
      init : {i : I} (f : Op P i) → Oper 0 (idx i) 
      then : {i : Sort 0} {f : Oper 0 i} (w : Tr 0 i) (α : Frm 0 w f) → Oper 1 (i , f) 
      smthg : {n : ℕ} {i : Sort n} {f : Oper n i} (w : Tr (S n) (i , f)) → Oper (S (S n)) ((i , f) , μ∞ n w)

    data Tr where
      inlf : {n : ℕ} (i : Sort n) → Tr n i
      innd : {n : ℕ} {i : Sort n} 
        → (f : Oper n i) (ϕ : (p : Params n f) → Tr n (τₚ n p))
        → Tr n i

    Params n f = {!!}
    Leaves n w = {!!}

    τₚ = {!!}
    τₗ = {!!}

    μ∞ = {!!}


