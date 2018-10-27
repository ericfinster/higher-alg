{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial

module MonoMagma where

  is-mono : ∀ {ℓ} {A B : Type ℓ} (f : A → B) → Type ℓ
  is-mono {B = B} f = (b : B) → is-prop (hfiber f b)

  -- This should be equivalent, right?
  is-emb : ∀ {ℓ} {A B : Type ℓ} (f : A → B) → Type ℓ
  is-emb {A = A} f = (x y : A) → is-equiv (ap f {x} {y})

  module _ {ℓ} {I : Type ℓ} (P : Poly I) (M : PolyMagma P) where

    open PolyMagma M
    
    mono-map : {i : I} (w : W P i) (f : Op P i) → f == μ w → Frame P w f
    mono-map w f idp = μ-frm w

    is-mono-magma : Type ℓ
    is-mono-magma = {i : I} (w : W P i) (f : Op P i) → is-emb (mono-map w f)


  module _ {ℓ} {I : Type ℓ} (P : Poly I) where

    open import Substitution P
    open PolyMagma subst-mgm
    
    -- So, the question is, is the substitution monad monic in the sense
    -- described above?
  
    conj : is-mono-magma Subst subst-mgm
    conj pd (w , α) p q = {!!}

    -- Agreed, so it seems like it should come down to the lemma
    -- that you imagined: there is an equivalence between
    -- endo equivalences of flatten and endo-equivalences of
    -- the baez-dolan frame.

    -- Could this in fact be correct?
