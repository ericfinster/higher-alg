{-# OPTIONS --without-K --rewriting --no-positivity #-}

open import HoTT
open import Util
open import Polynomial
open import Substitution

-- I have turned off positivity so as to be able to adapt old
-- code to this setup quickly for testing.  However, the non-
-- positivity can be avoided by using the three-field variant
-- of polynomials.  But grafting, substitution and so on would
-- need to be rewritten ...

module Indexed {ℓ} {I : Type ℓ} (P : Poly I) where

  Sort : ℕ → Type ℓ
  SPoly : (n : ℕ) → Poly (Sort n)

  data Oper : (n : ℕ) → Sort n → Type ℓ
  Params : (n : ℕ) {i : Sort n} (f : Oper n i) (j : Sort n) → Type ℓ

  Sort 0 = Ops P
  Sort (S n) = Σ (Sort n) (Oper n)

  Op (SPoly n) = Oper n
  Param (SPoly n) = Params n
  
  -- The hypothetical multiplication 
  μ∞ : (n : ℕ) {i : Sort n} → W (SPoly n) i → Oper n i

  data Oper where
    frm : {i : I} {f : Op P i} (w : W P i) (α : Frame P w f) → Oper 0 (i , f)
    web : {n : ℕ} {i : Sort n} (w : W (SPoly n) i) → Oper (S n) (i , μ∞ n w)

  Params O (frm w α) = Node P w 
  Params (S n) (web w) = Node (SPoly n) w 

  subst₀ : {i : I} (w : W P i)
    → (κ : (g : Ops P) → Node P w g → W (SPoly 0) g)
    → W P i
  subst₀ = {!!}

  subst : (n : ℕ) {i : Sort n} (w : W (SPoly n) i)
    → (κ : (g : Sort (S n)) → Node (SPoly n) w g → W (SPoly (S n)) g)
    → W (SPoly n) i
  subst n w = {!!}

  μ∞ O (lf (i , f)) = frm (corolla P f) (corolla-lf-eqv P f)
  μ∞ O (nd (frm w α , κ)) = frm (subst₀ w κ ) {!!}
  μ∞ (S n) (lf (i , f)) = transport (Oper (S n)) {!!} (web (corolla (SPoly n) f))
  μ∞ (S n) (nd (web w , κ)) = transport (Oper (S n)) {!!} (web (subst n w κ))
  


