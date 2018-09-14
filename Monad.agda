{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Substitution
open import SubstCoh

module Monad where

  -- We think of A as an "admissibility relation"
  record OpetopicType {ℓ} {I : Type ℓ} (P : Poly I) (A : PolyRel P) : Type (lsucc ℓ) where
    coinductive
    field
    
      Ref : Refinement A
      Hom : OpetopicType (P // ΣR A Ref) (FlattenRel (ΣR A Ref))

  open OpetopicType public

  record is-algebraic {ℓ} {I : Type ℓ} {P : Poly I} {R : PolyRel P} (X : OpetopicType P R) : Type ℓ where
    coinductive
    field

      is-mult : is-multiplicative P (ΣR R (Ref X))
      hom-is-alg : is-algebraic (Hom X)

  open is-algebraic public
  
  -- Some basic coherences
  module _ {ℓ} {I : Type ℓ} {P : Poly I} {R : PolyRel P}
    (T : OpetopicType P R) (is-alg : is-algebraic T) where

    μ : {i : I} (w : W P i) → Op P i
    μ w = fst (contr-center (is-mult is-alg w))

    η : (i : I) → Op P i
    η i = μ (lf i)

    WitRel : PolyRel P 
    WitRel = ΣR R (Ref T) 

    CohRel : PolyRel (P // WitRel)
    CohRel = ΣR (FlattenRel WitRel) (Ref (Hom T))

    μ-coh : {i : I} {f : Op P i} (w : W (P // WitRel) (i , f)) → Op (P // WitRel) (i , f)
    μ-coh w = fst (contr-center (is-mult (hom-is-alg is-alg) w))

    -- Nice!  So this is now completely general!!
    μ-flatten : {i : I} {f : Op P i} (w : W (P // WitRel) (i , f)) → μ (flatten WitRel w) == f
    μ-flatten {i} {f} pd = fst= (contr-path (is-mult is-alg (flatten WitRel pd)) lem₅)

      where lem₀ : Composite (P // WitRel) CohRel pd
            lem₀ = contr-center (is-mult (hom-is-alg is-alg) pd)

            lem₁ : flatten WitRel pd == fst (μ-coh pd)
            lem₁ = fst= (fst= (snd (fst (snd (snd lem₀))))) 

            lem₂ : flatten-frm WitRel pd == fst (snd (μ-coh pd)) [ (λ w₀ → Frame P w₀ f) ↓ lem₁ ]
            lem₂ = ↓-Σ-fst (snd= (fst= (snd (fst (snd (snd lem₀))))))
            
            lem₃ : WitRel (fst (μ-coh pd)) f (fst (snd (μ-coh pd)))
            lem₃ = snd (snd (μ-coh pd))

            lem₄ : WitRel (flatten WitRel pd) f (flatten-frm WitRel pd) 
            lem₄ = transport! (λ x → WitRel (fst x) f (snd x)) (pair= lem₁ lem₂) lem₃

            lem₅ : Composite P WitRel (flatten WitRel pd)
            lem₅ = f , flatten-frm WitRel pd , lem₄ 

    unit-r : (i : I) (f : Op P i) → μ (corolla P f) == f
    unit-r i f = μ-flatten (lf (i , f))

