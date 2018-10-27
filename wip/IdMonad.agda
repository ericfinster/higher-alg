{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Substitution
open import SubstCoh
open import Monad
open import Globularity
open import SetMonad

-- The Identity Monad
module IdMonad where

  IdPoly : Poly ⊤
  Op IdPoly _ = ⊤
  Param IdPoly _ _ = ⊤

  id-is-multip : {u : ⊤} (w : W IdPoly u) → is-contr (Composite IdPoly (λ w f α → ⊤) w)
  id-is-multip w = Σ-level Unit-level (λ f →
    Σ-level (Frame-level IdPoly Unit-level
                         (λ _ → Σ-level Unit-level (λ _ → Unit-level)) w f)
                         (λ _ → Unit-level))
  
  IdSetMnd : SetMonad IdPoly (λ w f α → ⊤)
  SetMonad.sort-is-gpd IdSetMnd = Unit-level
  SetMonad.op-is-set IdSetMnd _ = Unit-level
  SetMonad.arity-is-set IdSetMnd _ = Σ-level Unit-level (λ _ → Unit-level)
  SetMonad.rel-is-prop IdSetMnd _ _ _ = Unit-level
  SetMonad.is-multip IdSetMnd = id-is-multip
  SetMonad.laws IdSetMnd _ _ = tt , lift tt

  IdType : OpetopicType IdPoly (λ w f α → ⊤)
  IdType = MndType IdPoly (λ w f α → ⊤) IdSetMnd
