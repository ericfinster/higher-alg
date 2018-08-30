{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial

module SetMonad where

  PolyMagma : ∀ {ℓ} {I : Type ℓ} (P : Poly I) → Type ℓ
  PolyMagma {I = I} P = {i : I} (w : W P i) → Σ (Op P i) (Frame P w)

  module _ {ℓ} {I : Type ℓ} (P : Poly I) where

    Fr : Poly I
    Op Fr = W P
    Param Fr w = Leaf P w

    fr-mult : {i : I} (u : W Fr i) → W P i
    fr-mult (lf i) = lf i
    fr-mult (nd (w , ψ)) = graft P w (λ j l → fr-mult (ψ j l))

    fr-frm : {i : I} (u : W Fr i) → Frame Fr u (fr-mult u)
    fr-frm (lf i) j = ide (i == j)
    fr-frm (nd (w , ψ)) j = (graft-leaf-eqv P w (λ j l → fr-mult (ψ j l)) j)⁻¹ ∘e
      (Σ-emap-r (λ k → Σ-emap-r (λ l → fr-frm (ψ k l) j)))

    fr-magma : PolyMagma Fr
    fr-magma u = fr-mult u , fr-frm u


  module _ {ℓ} {I : Type ℓ} (P : Poly I)
    (op-set : (i : I) → is-set (Op P i))
    (param-set : {i : I} (f : Op P i) (j : I) → is-set (Param P f j)) where


    -- And then how should we state the axioms?
    -- SetAxioms : Type ℓ
    -- SetAxioms = {i : I} (w : W (Fr P) i) → {!!}

    -- Right.  We need the multiplication in the free monad, which,
    -- of course we can easily define.

    -- Right.
