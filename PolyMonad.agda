{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Substitution

module PolyMonad where

  --
  --  Polynomial Magmas
  --

  record PolyMagma {ℓ} {I : Type ℓ} (P : Poly I) : Type ℓ where
    constructor mgm
    field
      μ : {i : I} (w : W P i) → Op P i
      μ-frm : {i : I} (w : W P i) → Frame P w (μ w)

  open PolyMagma public

  --
  -- The slice of a polynomial by a magma
  --
  
  _//_ : ∀ {ℓ} {I : Type ℓ} (P : Poly I) (M : PolyMagma P) → Poly (Σ I (Op P))
  Op (P // M) (i , f) = Σ (W P i) (λ w → Σ (Frame P w f) (λ α → (μ M w , μ-frm M w) == (f , α))) 
  Param (P // M) (w , _ , _) = Node P w
  
  module _ {ℓ} {I : Type ℓ} {P : Poly I} (M : PolyMagma P) where

    slc-flatn : {i : I} {f : Op P i} → W (P // M) (i , f) → W P i
    slc-flatn-frm : {i : I} {f : Op P i} (pd : W (P // M) (i , f)) → Frame P (slc-flatn pd) f

    slc-flatn (lf (i , f)) = corolla P f
    slc-flatn (nd ((w , α , e) , κ)) =
      let κ' g n = slc-flatn (κ g n) , slc-flatn-frm (κ g n)
      in subst P w κ'

    slc-flatn-frm (lf (i , f)) = corolla-frm P f
    slc-flatn-frm (nd ((w , α , e) , κ)) j =
      let κ' g n = slc-flatn (κ g n) , slc-flatn-frm (κ g n)
      in α j ∘e (subst-lf-eqv P w κ' j)
    
    slc-bd-frame-to : {f : Ops P} (pd : W (P // M) f)
      → (g : Ops P) → Leaf (P // M) pd g → Node P (slc-flatn pd) g
    slc-bd-frame-to (lf i) ._ idp = inl idp
    slc-bd-frame-to (nd ((w , α , e) , κ)) g (h , n , l) = 
      subst-nd-from P w (λ g n → slc-flatn (κ g n) , slc-flatn-frm (κ g n)) g
        (h , n , slc-bd-frame-to (κ h n) g l)

    slc-bd-frame-from : {f : Ops P} (pd : W (P // M) f)
      → (g : Ops P) → Node P (slc-flatn pd) g → Leaf (P // M) pd g 
    slc-bd-frame-from (lf i) .i (inl idp) = idp
    slc-bd-frame-from (lf i) g (inr (j , p , ())) 
    slc-bd-frame-from (nd ((w , α , e) , κ)) g n = 
      let (h , n₀ , n₁) = subst-nd-to P w (λ g n → slc-flatn (κ g n) , slc-flatn-frm (κ g n)) g n
      in h , n₀ , slc-bd-frame-from (κ h n₀) g n₁

    postulate

      slc-bd-frame-to-from : {f : Ops P} (pd : W (P // M) f)
        → (g : Ops P) (n : Node P (slc-flatn pd) g)
        → slc-bd-frame-to pd g (slc-bd-frame-from pd g n) == n

      slc-bd-frame-from-to : {f : Ops P} (pd : W (P // M) f)
        → (g : Ops P) (l : Leaf (P // M) pd g)
        → slc-bd-frame-from pd g (slc-bd-frame-to pd g l) == l

    slc-bd-frm : {f : Ops P} (pd : W (P // M) f) 
      → (g : Ops P) → Leaf (P // M) pd g ≃ Node P (slc-flatn pd) g
    slc-bd-frm pd g = equiv (slc-bd-frame-to pd g) (slc-bd-frame-from pd g)
      (slc-bd-frame-to-from pd g) (slc-bd-frame-from-to pd g)

  CohWit : ∀ {ℓ} {I : Type ℓ} {P : Poly I} (M : PolyMagma P) → Type ℓ
  CohWit {ℓ} {I} {P} M = {i : I} {f : Op P i} (pd : W (P // M) (i , f))
    → Path {A = Σ (Op P i) (Frame P (slc-flatn M pd))}
           (μ M (slc-flatn M pd) , μ-frm M (slc-flatn M pd))
           (f , slc-flatn-frm M pd)

  SlcMgm : ∀ {ℓ} {I : Type ℓ} {P : Poly I} {M : PolyMagma P}
    → CohWit M → PolyMagma (P // M)
  μ (SlcMgm {M = M} Ψ) pd = slc-flatn M pd , slc-flatn-frm M pd , Ψ pd
  μ-frm (SlcMgm {M = M} Ψ) = slc-bd-frm M
  
  record CohStruct {ℓ} {I : Type ℓ} {P : Poly I} (M : PolyMagma P) : Type ℓ where
    coinductive
    field
    
      Ψ : CohWit M
      H : CohStruct (SlcMgm Ψ)

  open CohStruct

  -- -- A polynomial monad is a pair of a magma and
  -- -- a coherence structure on that magma.
  -- record PolyMonad {ℓ} {I : Type ℓ} (P : Poly I) : Type ℓ where
  --   field
  --     Mgm : PolyMagma P
  --     Coh : CohStruct P Mgm
