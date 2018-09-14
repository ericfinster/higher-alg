{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Substitution
open import SubstCoh
open import Monad
open import Globularity

-- Opetopes and their realizations
module Opetopes {ℓ} {I : Type ℓ} (P : Poly I) (X : OpetopicType P (FrameRel P)) where

  Opetope : ℕ → Type ℓ
  
  OpPoly : (n : ℕ) → Poly (Opetope n)
  OpRel : (n : ℕ) → PolyRel (OpPoly n)
  OpType : (n : ℕ) → OpetopicType (OpPoly n) (OpRel n)

  Opetope O = I
  Opetope (S n) = Ops (OpPoly n)

  OpPoly O = P
  OpPoly (S n) = OpPoly n // ΣR (OpRel n) (Ref (OpType n))

  OpRel O = FrameRel P
  OpRel (S n) = FlattenRel (ΣR (OpRel n) (Ref (OpType n)))

  OpType O = X
  OpType (S n) = Hom (OpType n)

  ∂Op : (n : ℕ) {o : Opetope n} (p : Op (OpPoly n) o) → Type ℓ
  ●Op : (n : ℕ) {o : Opetope n} (p : Op (OpPoly n) o) → Type ℓ
  in-∂Op : (n : ℕ) {o : Opetope n} (p : Op (OpPoly n) o) → ∂Op n p → ●Op n p

  ∂W : (n : ℕ) {o : Opetope n} (w : W (OpPoly n) o) → Type ℓ
  ●W : (n : ℕ) {o : Opetope n} (w : W (OpPoly n) o) → Type ℓ
  in-∂W : (n : ℕ) {o : Opetope n} (w : W (OpPoly n) o) → ∂W n w → ●W n w

  -- Exactly!
  ∂-equiv : (n : ℕ) {o : Opetope n} (p : Op (OpPoly n) o)
    → (w : W (OpPoly n) o) (α : Frame (OpPoly n) w p) (r : OpRel n w p α)
    -- → (r : ΣR (OpRel n) (Ref (OpType n)) w p α)
    → ∂Op n p ≃ ∂W n w

  ∂Op O f = ⊤ ⊔ Arity P f
  ∂Op (S n) {o , p} (w , α , r) =
    Pushout (span (●Op n p) (●W n w) (∂Op n p)
                  (in-∂Op n p)
                  ((in-∂W n w) ∘ –> (∂-equiv n p w α (fst r))))

  ●Op n p = ⊤ * (∂Op n p) 
  in-∂Op n p = jright

  -- And here's where I think we will have to work...
  ∂-equiv = {!!}

  -- Now, what is the ∂ of a successor tree?
  ∂W O w = ⊤ ⊔ Σ I (Leaf P w)
  ∂W (S n) {o , p} w = {!!}

    where canopy : W (OpPoly n) o
          canopy = flatten (ΣR (OpRel n) (Ref (OpType n))) w

          canopy-frm : Frame (OpPoly n) canopy p
          canopy-frm = flatten-frm (ΣR (OpRel n) (Ref (OpType n))) w

  ●W O (lf i) = Lift ⊤
  ●W O (nd (f , ϕ)) = ⊤ * (Σ (Arity P f) (λ a → ●W O (ϕ (fst a) (snd a))))
  ●W (S n) w = {!!}

  -- Excellent!!
  in-∂W O (lf i) (inl tt) = lift tt
  in-∂W O (lf i) (inr (.i , idp)) = lift tt
  in-∂W O (nd (f , ϕ)) (inl tt) = jleft tt
  in-∂W O (nd (f , ϕ)) (inr (j , k , p , l)) =
    jright ((k , p) , (in-∂W O (ϕ k p) (inr (j , l))))
  in-∂W (S n) w = {!!}

  -- The realization of an opetope is always just the filled
  -- version of itself viewed as an operation as above...
  𝕆 : {n : ℕ} → Opetope n → Type ℓ
  𝕆 {O} i = Lift ⊤
  𝕆 {S n} (o , p) = ●Op n p
