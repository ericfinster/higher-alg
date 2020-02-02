{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import PolyMagma
open import Grafting
open import Substitution
open import Slice

module wip.Globularity {ℓ} {I : Type ℓ} (P : Poly I) where

  NColors : ℕ → Type ℓ
  NPoly : (n : ℕ) → Poly (NColors n)
  NRel : (n : ℕ) → PolyRel (NPoly n)
  NGlobular : (n : ℕ) → Type ℓ
  NMagma : (n : ℕ) → NGlobular n → PolyMagma (NPoly (S n))

  NColors O = Ops P
  NColors (S n) = Ops (NPoly n)
  
  NPoly O = Subst P
  NPoly (S n) = NPoly n // NRel n

  NRel O = ⟪ SubstMgm P ⟫
  NRel (S n) = {!!}

  NGlobular O = SubInvar (Subst P) ⟪ SubstMgm P ⟫ 
  NGlobular (S n) = {!!}

  NMagma O g = SlcMgm (Subst P) ⟪ SubstMgm P ⟫ g
  NMagma (S n) g = {!!}
