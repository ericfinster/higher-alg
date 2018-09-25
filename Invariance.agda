{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Substitution

module Invariance where

  -- Okay, I want to state some kind of invariance lemma
  -- and see if I can build on it.

  module _ {ℓ} {I : Type ℓ} {P : Poly I} (R : PolyRel P) where

    postulate

      loop-fam : {i : I} {f : Op P i}
        → (w : W P i) (α : Frame P w f) (r : R w f α)
        → r == r

    -- Okay, so we know a collection of loops in our family
    -- We should get an endomorphism of every pasting diagram, right?

    pd-endo : {i : I} {f : Op P i}
      → (pd : W (P // R) (i , f))
      → pd == pd
    pd-endo (lf .(_ , _)) = idp
    pd-endo (nd ((w , α , r) , ϕ)) = ap (λ x → nd ((w , α , (fst x)) , (snd x)))
      (pair= (loop-fam w α r) (↓-cst-in ϕ-endo))

      where ϕ-endo : ϕ == ϕ
            ϕ-endo = λ= (λ g → λ= (λ n → pd-endo (ϕ g n)))

    -- Okay, good.
    -- And now, what is my claim?

    invar : {i : I} {f : Op P i}
      → (pd : W (P // R) (i , f))
      → ap (flatten R) (pd-endo pd) == idp
    invar (lf .(_ , _)) = idp
    invar (nd ((w , α , r) , ϕ)) = lem

      where lem = ap (flatten R)
                     (ap (λ x → nd ((w , α , fst x) , snd x))
                         (pair= (loop-fam w α r) (↓-cst-in (λ= (λ g → λ= (λ n → pd-endo (ϕ g n))))))) =⟨ {!!} ⟩
                  ap (λ x → flatten R (nd ((w , α , fst x) , snd x)))
                    (pair= (loop-fam w α r) (↓-cst-in (λ= (λ g → λ= (λ n → pd-endo (ϕ g n)))))) =⟨ idp ⟩
                  ap (λ x → substitute R w (snd x)) 
                    (pair= (loop-fam w α r) (↓-cst-in (λ= (λ g → λ= (λ n → pd-endo (ϕ g n)))))) =⟨ {!!} ⟩
                  ap (substitute R w) (λ= (λ g → λ= (λ n → pd-endo (ϕ g n)))) =⟨ {!!} ⟩ 
                  idp ∎

    -- Well, okay, so there should be some kind of commutation with
    -- equality of decorations and whatnot, but it should be quite
    -- clear that this is going to come out fine.....
