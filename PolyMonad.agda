{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Substitution

module PolyMonad where

  -- A polynomial sliced by a relation
  module _ {ℓ} {I : Type ℓ} {P : Poly I} (R : PolyRel P) where

    flatn : {i : I} {f : Op P i} → W (P // R) (i , f) → W P i
    flatn-frm : {i : I} {f : Op P i} (w : W (P // R) (i , f)) → Frame P (flatn w) f

    flatn (lf (i , f)) = corolla P f
    flatn (nd (((w , α) , r) , κ)) = 
      let κ' g n = flatn (κ g n) , flatn-frm (κ g n)
      in subst P w κ'

    flatn-frm (lf (i , f)) = corolla-frm P f
    flatn-frm (nd (((w , α) , r) , κ)) j =
      let κ' g n = flatn (κ g n) , flatn-frm (κ g n)
      in α j ∘e subst-lf-eqv P w κ' j

    bd-frame-to : {f : Ops P} (pd : W (P // R) f)
      → (g : Ops P) → Leaf (P // R) pd g → Node P (flatn pd) g
    bd-frame-to (lf (i , f)) (j , g) l = inl l
    bd-frame-to (nd (((w , α) , r) , κ)) g (h , n , l) =
      let κ' g n = flatn (κ g n) , flatn-frm (κ g n)
      in subst-nd-from P w κ' g
         (h , n , bd-frame-to (κ h n) g l)

    bd-frame-from : {f : Ops P} (pd : W (P // R) f)
      → (g : Ops P) → Node P (flatn pd) g → Leaf (P // R) pd g 
    bd-frame-from (lf (i , f)) g (inl n) = n
    bd-frame-from (lf (i , f)) g (inr (j , p , ())) 
    bd-frame-from (nd (((w , α) , r) , κ)) g n = 
      let κ' g n = flatn (κ g n) , flatn-frm (κ g n)
          (h , n₀ , n₁) = subst-nd-to P w κ' g n
      in h , n₀ , bd-frame-from (κ h n₀) g n₁

    postulate

      bd-frame-to-from : {f : Ops P} (pd : W (P // R) f)
        → (g : Ops P) (n : Node P (flatn pd) g)
        → bd-frame-to pd g (bd-frame-from pd g n) == n

      bd-frame-from-to : {f : Ops P} (pd : W (P // R) f)
        → (g : Ops P) (l : Leaf (P // R) pd g)
        → bd-frame-from pd g (bd-frame-to pd g l) == l

    bd-frm : {f : Ops P} (pd : W (P // R) f)
      → (g : Ops P) → Leaf (P // R) pd g ≃ Node P (flatn pd) g
    bd-frm pd g = equiv (bd-frame-to pd g) (bd-frame-from pd g)
      (bd-frame-to-from pd g) (bd-frame-from-to pd g)

    -- A relation is invariant by subdivision if we can
    -- find an element for the flattened tree and frame
    SubInvar : Type ℓ
    SubInvar = {f : Ops P} (pd : W (P // R) f) → R f (flatn pd , flatn-frm pd)

  -- An invariant relation induces a magma
  SlcMgm : ∀ {ℓ} {I : Type ℓ} {P : Poly I} {R : PolyRel P}
    → SubInvar R → PolyMagma (P // R)
  μ (SlcMgm {R = R} Ψ) pd = (flatn R pd , flatn-frm R pd) , Ψ pd
  μ-frm (SlcMgm {R = R} Ψ) pd = bd-frm R pd

  record CohStruct {ℓ} {I : Type ℓ} {P : Poly I} (M : PolyMagma P) : Type ℓ where
    coinductive
    field
    
      Ψ : SubInvar (MgmRel M)
      H : CohStruct (SlcMgm Ψ)

  open CohStruct public
