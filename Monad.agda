{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Substitution

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
  
  --
  --  Some basic coherences
  --
  
  -- module _ {ℓ} {I : Type ℓ} {P : Poly I} {C : CartesianRel P}
  --   (T : OpetopicType P C) (is-alg : is-algebraic T) where

  --   μ : {i : I} (w : W P i) → Op P i
  --   μ w = fst (contr-center (is-mult is-alg w))

  -- --   μ-frm : {i : I} (w : W P i) (j : I) → Leaf P w j ≃ Param P (μ w) j
  -- --   μ-frm w = fst (snd (contr-center (is-fillable is-alg w)))

  -- --   μ-witness : {i : I} (w : W P i) → (Rl D) w (μ w) (μ-frm w)
  -- --   μ-witness w = snd (snd (contr-center (is-fillable is-alg w))) 

  --   η : (i : I) → Op P i
  --   η i = μ (lf i)

  -- --   ηρ-eqv : (i : I) (j : I) → Leaf P (lf i) j ≃ Param P (η i) j
  -- --   ηρ-eqv i = μ-frm (lf i)

  --   -- ηρ-contr : (i : I) → is-contr (Σ I (Param P (η i)))
  --   -- ηρ-contr i = equiv-preserves-level (Σ-emap-r (ηρ-eqv i)) ⦃ lf-lf-contr P i ⦄

  --   WitRel : CartesianRel P 
  --   WitRel = ΣRef C (Ref T) 

  --   HomRel : CartesianRel (P // fst WitRel)
  --   HomRel = ΣRef (FlattenRel WitRel) (Ref (Hom T))

  --   μ-coh : {i : I} {f : Op P i} (w : W (P // fst WitRel) (i , f)) → Op (P // fst WitRel) (i , f)
  --   μ-coh w = fst (contr-center (is-mult (hom-is-alg is-alg) w))

  --   -- Nice!  So this is now completely general!!
  --   μ-flatten : {i : I} {f : Op P i} (w : W (P // fst WitRel) (i , f)) → μ (flatten WitRel w) == f
  --   μ-flatten {i} {f} pd = fst= (contr-path (is-mult is-alg (flatten WitRel pd)) lem₄)

  --     where lem₀ : Composite (P // fst WitRel) HomRel pd
  --           lem₀ = contr-center (is-mult (hom-is-alg is-alg) pd)

  --           lem₁ : flatten WitRel pd == fst (μ-coh pd)
  --           lem₁ = fst (snd lem₀)

  --           lem₂ : fst WitRel (fst (μ-coh pd)) f
  --           lem₂ = snd (μ-coh pd)

  --           lem₃ : fst WitRel (flatten WitRel pd) f
  --           lem₃ = transport! (λ x → fst WitRel x f) lem₁ lem₂

  --           lem₄ : Composite P WitRel (flatten WitRel pd)
  --           lem₄ = f , lem₃

  --   unit-r : (i : I) (f : Op P i) → μ (corolla P f) == f
  --   unit-r i f = μ-flatten (lf (i , f))

