{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Substitution
open import Monad

module Magma where

  -- This is the same as a map which creates composites.  Given such a thing,
  -- there is a canonical refinement, namely that of being equal to the
  -- chosen composite.
  record PolyMagma {ℓ} {I : Type ℓ} (P : Poly I) (R : PolyRel P) : Type ℓ where
    field

      mult : {i : I} (w : W P i) → Op P i
      mult-frm : {i : I} (w : W P i) → Frame P w (mult w)
      mult-rel : {i : I} (w : W P i) → R w (mult w) (mult-frm w)

  open PolyMagma public

  MgmRef : ∀ {ℓ} {I : Type ℓ} {P : Poly I} {R : PolyRel P}
    → PolyMagma P R → Refinement R
  MgmRef M w f α r = (mult M w , mult-frm M w , mult-rel M w) == (f , α , r)

  MgmRef-level : ∀ {ℓ n} {I : Type ℓ} {P : Poly I} {R : PolyRel P} (M : PolyMagma P R)
    → (op-set : (i : I) → has-level (S n) (Op P i))
    → (frm-set : {i : I} (w : W P i) (f : Op P i) → has-level (S n) (Frame P w f))
    → (rel-set : {i : I} (w : W P i) (f : Op P i) (α : Frame P w f) → has-level (S n) (R w f α))
    → {i : I} (w : W P i) (f : Op P i) (α : Frame P w f) (r : R w f α)
    → has-level n (MgmRef M w f α r)
  MgmRef-level M os fs rs w f α r = has-level-apply
    (Σ-level (os _) (λ g → Σ-level (fs w g) (λ β → rs w g β)))
    (mult M w , mult-frm M w , mult-rel M w)
    (f , α , r)

  mgm-is-mult : ∀ {ℓ} {I : Type ℓ} {P : Poly I} {R : PolyRel P}
    → (M : PolyMagma P R) → is-multiplicative P (ΣR R (MgmRef M))
  mgm-is-mult {P = P} {R = R} M w = has-level-in (ctr , pth) 

    where ctr : Composite P (ΣR R (MgmRef M)) w
          ctr = mult M w , mult-frm M w , mult-rel M w , idp

          pth : (c : Composite P (ΣR R (MgmRef M)) w) → ctr == c
          pth (._ , ._ , ._ , idp) = idp
          

  -- record CoherentMnd {ℓ} {I : Type ℓ} (P : Poly I) (C : CartesianRel P) : Type ℓ where
  --   field

  --     mgm : PolyMagma P C

  --     coh : {i : I} (f : Op P i) (w : W P i)
  --       → is-prop (fst (ΣRef C (MgmExt P C mgm)) w f)
      
  --     lws : {i : I} (f : Op P i) (pd : W (P // fst (ΣRef C (MgmExt P C mgm))) (i , f))
  --       → fst (ΣRef C (MgmExt P C mgm)) (flatten (ΣRef C (MgmExt P C mgm)) pd) f

  -- -- Okay, and the conjecture is that the above suffices.
  -- -- What does that mean?

  -- module _ {ℓ} {I : Type ℓ} (P : Poly I) (C : CartesianRel P) (M : CoherentMnd P C) where

  --   open CoherentMnd M
    
  --   private
  --     R = ΣRef C (MgmExt P C mgm)

  --   HCPoly : Poly (Ops P)
  --   HCPoly = P // fst R

  --   HCMgm : PolyMagma HCPoly (FlattenRel R)
  --   mult HCMgm {_ , f} w = flatten R w , lws f w
  --   mult-rel HCMgm w = idp

  --   hom-coh : (f : Ops P) (w : Op HCPoly f) (pd : W HCPoly f)
  --     → is-prop (fst (ΣRef (FlattenRel R) (MgmExt HCPoly (FlattenRel R) HCMgm)) pd w)
  --   hom-coh (i , f) (w , r , e) pd = {!!}

