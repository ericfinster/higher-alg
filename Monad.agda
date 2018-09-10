{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Substitution

module Monad where

  Refinement : ∀ {ℓ} {I : Type ℓ} {P : Poly I} (C : CartesianRel P) → Type (lsucc ℓ)
  Refinement {ℓ} {I} {P} C = {i : I} {w : W P i} {f : Op P i} (r : fst C w f) → Type ℓ

  ΣRef : ∀ {ℓ} {I : Type ℓ} {P : Poly I} (C : CartesianRel P)
    → Refinement C
    → CartesianRel P
  ΣRef C R = (λ w f → Σ (fst C w f) R) , (λ w f r → snd C w f (fst r))

  Composite : ∀ {ℓ} {I : Type ℓ} {P : Poly I}
    → (C : CartesianRel P)
    → {i : I} (w : W P i) → Type ℓ
  Composite {P = P} C {i} w = Σ (Op P i) (λ f → fst C w f)

  is-multiplicative : ∀ {ℓ} {I : Type ℓ} {P : Poly I}
    → (C : CartesianRel P) → Type ℓ
  is-multiplicative {I = I} {P = P} C =
    {i : I} (w : W P i) → is-contr (Composite C w)
  
  record OpetopicType {ℓ} {I : Type ℓ} (P : Poly I) (C : CartesianRel P) : Type (lsucc ℓ) where
    coinductive
    field

      Ref : Refinement C
      Hom : OpetopicType (P // fst (ΣRef C Ref)) (FlattenRel (ΣRef C Ref))

  open OpetopicType

  -- We'll have to come back to this example ....
  -- TerminalType : ∀ {ℓ} {I : Type ℓ} (P : Poly I) (C : CartesianRel P) → OpDom P C
  -- Fillers (TerminalDom P C) w f r = Lift ⊤
  -- HomDom (TerminalDom P C) = TerminalDom (P // fst C) (FlattenRel C)

  record is-algebraic {ℓ} {I : Type ℓ} {P : Poly I} {C : CartesianRel P} (T : OpetopicType P C) : Type ℓ where
    coinductive
    field

      is-mult : is-multiplicative (ΣRef C (Ref T))
      hom-is-alg : is-algebraic (Hom T)

  open is-algebraic
  
  --
  --  Some basic coherences
  --
  
  module _ {ℓ} {I : Type ℓ} {P : Poly I} (T : OpetopicType P (FrameRel P)) (is-alg : is-algebraic T) where

    μ : {i : I} (w : W P i) → Op P i
    μ w = fst (contr-center (is-mult is-alg w))

  --   μ-frm : {i : I} (w : W P i) (j : I) → Leaf P w j ≃ Param P (μ w) j
  --   μ-frm w = fst (snd (contr-center (is-fillable is-alg w)))

  --   μ-witness : {i : I} (w : W P i) → (Rl D) w (μ w) (μ-frm w)
  --   μ-witness w = snd (snd (contr-center (is-fillable is-alg w))) 

    η : (i : I) → Op P i
    η i = μ (lf i)

  --   ηρ-eqv : (i : I) (j : I) → Leaf P (lf i) j ≃ Param P (η i) j
  --   ηρ-eqv i = μ-frm (lf i)

    -- ηρ-contr : (i : I) → is-contr (Σ I (Param P (η i)))
    -- ηρ-contr i = equiv-preserves-level (Σ-emap-r (ηρ-eqv i)) ⦃ lf-lf-contr P i ⦄

    -- Okay, yeah, you'll need a bit more setup because you have to actually
    -- use the multiplication in the next dimension.

    HomRel : CartesianRel P 
    HomRel = ΣRef (FrameRel P) (Ref T) 

    BlorpRel : CartesianRel (P // fst HomRel)
    BlorpRel = ΣRef (FlattenRel HomRel) (λ {i} {pd} {w} r → Ref (Hom T) {i} {pd} {w} r)

    μ-coh : {i : I} {f : Op P i} (w : W (P // fst HomRel) (i , f)) → Op (P // fst HomRel) (i , f)
    μ-coh w = fst (contr-center (is-mult (hom-is-alg is-alg) w))

    -- Nice!  So this is now completely general!!
    μ-coh' : {i : I} {f : Op P i} (w : W (P // fst HomRel) (i , f)) → μ (flatten HomRel w) == f
    μ-coh' {i} {f} pd = fst= (contr-path (is-mult is-alg (flatten HomRel pd)) lem₄)

      where lem₀ : Composite BlorpRel pd
            lem₀ = contr-center (is-mult (hom-is-alg is-alg) pd)

            lem₁ : flatten HomRel pd == fst (μ-coh pd)
            lem₁ = fst (snd lem₀)

            lem₂ : fst HomRel (fst (μ-coh pd)) f
            lem₂ = snd (μ-coh pd)

            lem₃ : fst HomRel (flatten HomRel pd) f
            lem₃ = transport! (λ x → fst HomRel x f) lem₁ lem₂

            lem₄ : Composite HomRel (flatten HomRel pd)
            lem₄ = f , lem₃

    unit-r : (i : I) (f : Op P i) → μ (corolla P f) == f
    unit-r i f = μ-coh' (lf (i , f))

