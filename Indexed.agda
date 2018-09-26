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

  Sort 0 = I
  Sort (S n) = Σ (Sort n) (Oper n)

  SPoly O = P
  Op (SPoly (S n)) = Oper (S n)
  Param (SPoly (S n)) = Params (S n)

  -- The hypothetical multiplication in positive dimensions
  μ∞ : (n : ℕ) {i : Sort n} {f : Oper n i} 
    → W (SPoly (S n)) (i , f) → Oper (S n) (i , f)

  data Oper where
    op : {i : I} (f : Op P i) → Oper 0 i
    frm : {i : I} {f : Op P i} (w : W P i) (α : Frame P w f) → Oper 1 (i , op f) 
    web : {n : ℕ} {i : Sort n} {f : Oper n i} (w : W (SPoly (S n)) (i , f)) → Oper (S (S n)) ((i , f) , μ∞ n w)

  Params O (op f) = Param P f
  Params (S O) (frm w α) (i , op f) = Node P w (i , f)
  Params (S (S n)) (web w) = Node (SPoly (S n)) w 

  subst : (n : ℕ) {i : Sort n} (w : W (SPoly n) i)
    → (κ : (g : Sort (S n)) → Node (SPoly n) w (fst g , {!snd g!}) → W (SPoly (S n)) g)
    → W (SPoly n) i
  subst n w = {!!}

  μ∞ O (lf (i , op f)) = frm (corolla P f) (corolla-lf-eqv P f)
  μ∞ O {i} {op f} (nd (frm w α , κ)) = frm {!!} {!!}
  μ∞ (S n) w = {!!}


