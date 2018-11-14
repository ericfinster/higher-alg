{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Substitution
open import PolyMonad

-- Realizing opetopes
module wip.Opetopes {ℓ} {I : Type ℓ} {P : Poly I} (M : PolyMagma P) (C : CohStruct M) where
  
  Opetope : ℕ → Type ℓ
  
  OpPoly : (n : ℕ) → Poly (Opetope n)
  OpMagma : (n : ℕ) → PolyMagma (OpPoly n)
  OpCoh : (n : ℕ) → CohStruct (OpMagma n)

  Opetope O = I
  Opetope (S n) = Ops (OpPoly n)

  OpPoly O = P
  OpPoly (S n) = OpPoly n // MgmRel (OpMagma n) 

  OpMagma O = M
  OpMagma (S n) = SlcMgm (Ψ (OpCoh n))

  OpCoh O = C
  OpCoh (S n) = H (OpCoh n)
  
  ∂𝕆 : (n : ℕ) → Opetope n → Type ℓ
  𝕎 : (n : ℕ) {i : Opetope n} → W (OpPoly n) i → Type ℓ
  ∂⁻ : (n : ℕ) {i : Opetope n} (f : Op (OpPoly n) i) → Type ℓ

  𝕆 : (n : ℕ) → Opetope n → Type ℓ
  𝕆 n i = ⊤ * ∂𝕆 n i
  
  in-∂⁻-Op : (n : ℕ) {i : Opetope n} (f : Op (OpPoly n) i)
    → (j : Opetope n) (p : Param (OpPoly n) f j)
    → 𝕆 n j → ∂⁻ n f

  in-∂⁺-W : (n : ℕ) {i : Opetope n} (w : W (OpPoly n) i)
    → 𝕆 n i → 𝕎 n w

  in-∂⁻ : (n : ℕ) {i : Opetope n} (f : Op (OpPoly n) i)
    → ∂𝕆 n i → ∂⁻ n f

  ∂⁻ O f = Arity P f
  ∂⁻ (S n) ((w , α) , r) = 𝕎 n w

  ∂𝕆 O i = Lift ⊥
  ∂𝕆 (S n) (i , f) = Pushout (span (𝕆 n i) (∂⁻ n f) (∂𝕆 n i) jright (in-∂⁻ n f))

  𝕎 n (lf i) = 𝕆 n i
  𝕎 n (nd {i} (f , ϕ)) = 
    let ispace = Σ (Opetope n) (λ j → Σ (Param (OpPoly n) f j) (λ p → 𝕆 n j))
        wspace = Σ (Opetope n) (λ j → Σ (Param (OpPoly n) f j) (λ p → 𝕎 n (ϕ j p)))
        ospace = ⊤ * Pushout (span (𝕆 n i) (∂⁻ n f) (∂𝕆 n i) jright (in-∂⁻ n f))
    in Pushout (span ospace wspace ispace 
      (λ { (j , p , x) → jright (right (in-∂⁻-Op n f j p x)) })
      (λ { (j , p , x) → j , p , in-∂⁺-W n (ϕ j p) x }))

  in-𝕎 : (n : ℕ) {i : Opetope n} (w : W (OpPoly n) i)
    → (g : Ops (OpPoly n)) (d : Node (OpPoly n) w g)
    → 𝕆 (S n) g → 𝕎 n w
  in-𝕎 n (lf i) g (lift ()) 
  in-𝕎 n (nd (f , ϕ)) .(_ , f) (inl idp) = left
  in-𝕎 n (nd (f , ϕ)) g (inr (k , p , d)) x =
    right (k , p , in-𝕎 n (ϕ k p) g d x)

  in-∂⁺-W n (lf i) x = x
  in-∂⁺-W n (nd (f , ϕ)) x = left (right (left x))

  {-# TERMINATING #-}
  in-∂⁻-Op O f j p _ = j , p
  in-∂⁻-Op (S n) ((w , α) , r) = in-𝕎 n w 

  in-∂⁻ O f (lift ())
  in-∂⁻ (S n) {i , f} ((w , α) , r) = {!!}

  -- Right.  So geometrically, this looks really, really good.
  -- This last guy should be the one that takes a bit of work.

  -- But I guess things can't quite stay in this form because
  -- of the stupid termination checker.


