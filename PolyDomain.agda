{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial

module PolyDomain where

  --
  --  Frames and FillingFamilies
  --
  
  Frame : {I : Type₀} (P : Poly I) {i : I} (w : W P i) (c : γ P i) → Type₀
  Frame {I} P w c = (j : I) → Leaf P w j ≃ ρ P c j

  FillingFamily : {I : Type₀} → Poly I → Type₁
  FillingFamily {I} P = {i : I} (w : W P i) (c : γ P i) → Frame P w c → Type₀

  _//_ : {I : Type₀} (P : Poly I) (F : FillingFamily P) → Poly (Σ I (γ P))
  γ (P // F) (i , c) = Σ (W P i) (λ w → Σ (Frame P w c) (F w c))
  ρ (P // F) (w , f , x) (j , d) = Node P w d

  filler-inv : {I : Type₀} {P : Poly I} (F : FillingFamily P)
    → {i : I} {w₀ w₁ : W P i} (p : w₀ == w₁)
    → (c : γ P i) → Σ (Frame P w₀ c) (F w₀ c) ≃ Σ (Frame P w₁ c) (F w₁ c)
  filler-inv F idp c = ide _

  --
  --  Polynomial Domains
  --
  
  record PolyDomain {I : Type₀} (P : Poly I) : Type₁ where
    coinductive
    field

      F : FillingFamily P 
      H : PolyDomain (P // F)

  open PolyDomain public
