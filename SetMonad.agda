{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial

module SetMonad where

  record PolyMagma {ℓ} {I : Type ℓ} (P : Poly I) : Type ℓ where
    field

      mult : {i : I} (w : W P i) → Op P i
      mult-frm : {i : I} (w : W P i) → Frame P w (mult w)

  open PolyMagma
  
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
    mult fr-magma = fr-mult
    mult-frm fr-magma = fr-frm

    ind-mult : (M : PolyMagma P) → {i : I} (u : W Fr i) → W P i
    ind-mult M (lf i) = lf i
    ind-mult M (nd (w , ψ)) = nd (mult M w , λ j p → ind-mult M (ψ j (<– (mult-frm M w j) p)))

    -- Annoying but obviously doable ...
    ind-mult-frm : (M : PolyMagma P) → {i : I} (u : W Fr i) → Frame Fr u (ind-mult M u)
    ind-mult-frm M (lf i) j = ide _
    ind-mult-frm M (nd (w , ψ)) j = equiv to from {!!} {!!}

      where A : Type ℓ
            A = Σ I (λ k → Σ (Leaf P w k) (λ p → Leaf Fr (ψ k p) j))

            B : Type ℓ
            B = Σ I (λ k → Σ (Param P (mult M w) k) (λ p → Leaf P (ind-mult M (ψ k (<– (mult-frm M w k) p))) j))

            to : A → B
            to (k , l₀ , l₁) = k , –> (mult-frm M w k) l₀ ,
              transport (λ x → Leaf P x j)
                        (ap (λ x → ind-mult M (ψ k x))
                        (! (<–-inv-l (mult-frm M w k) l₀))) (–> (ind-mult-frm M (ψ k l₀) j) l₁) 

            from : B → A
            from (k , p , l) = {!!}


  record SetMonad {ℓ} {I : Type ℓ} (P : Poly I) : Type ℓ where
    field

      op-is-set : (i : I) → is-set (Op P i)
      param-is-set : {i : I} (f : Op P i) (j : I) → is-set (Param P f j)

      mag : PolyMagma P
      
      assoc : {i : I} (u : W (Fr P) i) → mult mag (fr-mult P u) == mult mag (ind-mult P mag u)

      -- We just ask that the values agree, but this is enough that the
      -- frames are actually equal.
      assoc-frm : {i : I} (u : W (Fr P) i) (j : I) (l : Leaf (Fr P) u j)
        → fst (mult-frm mag (fr-mult P u) j) (fst (fr-frm P u j) l)
        == fst (mult-frm mag (ind-mult P mag u) j) (fst (ind-mult-frm P mag u j) l)
           [ (λ f → Param P f j) ↓ assoc u ]

