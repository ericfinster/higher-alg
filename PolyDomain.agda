{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Poly

module PolyDomain where

  Frame : {I : Type₀} (P : Poly I) {i : I} (w : W P i) (c : γ P i) → Type₀
  Frame {I} P w c = (j : I) → Leaf P w j ≃ ρ P c j

  _//_ : {I : Type₀} (P : Poly I) (F : {i : I} {w : W P i} {c : γ P i} → Frame P w c → Type₀) → Poly (Σ I (γ P))
  γ (P // F) (i , c) = Σ (W P i) (λ w → Σ (Frame P w c) F)
  ρ (P // F) (w , f , x) (j , d) = Node P w d

  record PolyDomain {I : Type₀} (P : Poly I) : Type₁ where
    coinductive
    field

      F : {i : I} {w : W P i} {c : γ P i} → Frame P w c → Type₀
      H : PolyDomain (P // F)

  open PolyDomain public
