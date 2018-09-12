{-# OPTIONS --without-K --rewriting --type-in-type #-}

open import HoTT
open import Util
open import Polynomial
open import Substitution
open import SubstCoh
open import Monad
open import Magma

-- Attempting to construct the terminal cart-poly-monad.
module Terminal where

  𝕌 : Poly ⊤
  Op 𝕌 unit = Type₀
  Param 𝕌 X unit = X

  TerminalType : ∀ {ℓ} {I : Type ℓ} (P : Poly I) (C : CartesianRel P) → OpetopicType P C
  Ref (TerminalType P C) w f r = Lift ⊤
  Hom (TerminalType P C) = TerminalType (P // fst (ΣRef C (λ w f r → Lift ⊤)))
                                        (FlattenRel (ΣRef C (λ w f r → Lift ⊤)))


  -- module _ {ℓ} {I : Type ℓ} {P : Poly I} {C : CartesianRel P} (is-m : is-multiplicative P C) where



  -- -- As a first step, and without any uniqueness, shouldn't it be the
  -- -- case that we at least have a multiplication?

  -- -- record is-algebraic {ℓ} {I : Type ℓ} {P : Poly I} {C : CartesianRel P} (T : OpetopicType P C) : Type ℓ where
  -- --   coinductive
  -- --   field

  -- --     is-mult : is-multiplicative P (ΣRef C (Ref T))
  -- --     hom-is-alg : is-algebraic (Hom T)


  -- module _ {ℓ} {I : Type ℓ} {P : Poly I} {C : CartesianRel P} (is-m : is-multiplicative P C) where

  --   private
  --     R = ΣRef C (λ w f r → Lift ⊤)

  --   -- comp-magma : PolyMagma (P // fst R) (FlattenRel R)
  --   -- mult comp-magma pd = flatten R pd , {!mult-rel M (flatten R pd) !} , lift tt
  --   -- mult-rel comp-magma pd = idp

  --   thm : is-multiplicative (P // fst R) (FlattenRel R)
  --   thm pd = has-level-in (ctr , pth)

  --     where ctr : Composite (P // fst R) (FlattenRel R) pd
  --           ctr = (flatten R pd , {!snd (contr-center (is-m (flatten R pd)))!} , lift tt) , {!!}

  --           pth : (c : Composite (P // fst R) (FlattenRel R) pd) → ctr == c
  --           pth c = {!!}

  -- record is-composable {ℓ} {I : Type ℓ} {P : Poly I} {C : CartesianRel P} (T : OpetopicType P C) : Type ℓ where
  --   coinductive
  --   field

  --     comp : {i : I} (w : W P i) → Σ (Op P i) (fst C w)
  --     hom-is-comp : is-composable (Hom T)

  -- conj : ∀ {ℓ} {I : Type ℓ} {P : Poly I} {C : CartesianRel P}
  --   → (M : PolyMagma P C)
  --   → is-composable (TerminalType P C)
  -- is-composable.comp (conj M) = {!!}
  -- is-composable.hom-is-comp (conj M) = {!!}

  -- --
  -- --  Yeah, this isn't working.  You need a new idea.
  -- --
