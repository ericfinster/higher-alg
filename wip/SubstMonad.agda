{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Biased

module wip.SubstMonad {ℓ} {I : Type ℓ} (P : Poly I) where

  -- The polynomial of tree substitutions
  SubstPoly : Poly (Ops P)
  Op SubstPoly = InFrame P 
  Param SubstPoly (w , _) g = Node P w g

  open BiasedMgm
  
  SubstBiasedMgm : BiasedMgm SubstPoly
  η SubstBiasedMgm = {!!}
  η-frm SubstBiasedMgm = {!!}
  γ SubstBiasedMgm = {!!}
  γ-frm SubstBiasedMgm = {!!}
