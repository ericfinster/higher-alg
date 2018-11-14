{-# OPTIONS --without-K --rewriting --type-in-type #-}

open import HoTT
open import Util
open import Polynomial
open import Substitution
open import PolyMonad
open import WPaths

module wip.Universe where

  𝕌 : Poly ⊤
  Op 𝕌 _ = Type₀
  Param 𝕌 X _ = X

  𝕌-Mgm : PolyMagma 𝕌
  μ 𝕌-Mgm w = Leaf 𝕌 w tt
  μ-frm 𝕌-Mgm w tt = ide (Leaf 𝕌 w tt)

  R = MgmRel 𝕌-Mgm

  postulate

    out-contr : (w : W 𝕌 tt) → is-contr (OutFrame 𝕌 w)

  𝕌-Sub : SubInvar (MgmRel 𝕌-Mgm)
  𝕌-Sub {i , X} w = contr-has-all-paths ⦃ out-contr (flatn R w) ⦄
    (μ 𝕌-Mgm (flatn R w) , μ-frm 𝕌-Mgm (flatn R w))
    (X , flatn-frm R w)

  -- SubInvar : Type ℓ
  -- SubInvar = {f : Ops P} (pd : W (P // R) f) → R (flatn pd , flatn-frm pd)

  -- -- An invariant relation induces a magma
  -- SlcMgm : ∀ {ℓ} {I : Type ℓ} {P : Poly I} {R : PolyRel P}
  --   → SubInvar R → PolyMagma (P // R)
  -- μ (SlcMgm {R = R} Ψ) pd = (flatn R pd , flatn-frm R pd) , Ψ pd
  -- μ-frm (SlcMgm {R = R} Ψ) pd = bd-frm R pd

    -- InFrame : Ops P → Type ℓ
    -- InFrame (i , f) = Σ (W i) (λ w → Frame w f)

    -- OutFrame : {i : I} → W i → Type ℓ
    -- OutFrame {i} w = Σ (Op P i) (Frame w)

  -- -- The relation induced by a magma
  -- MgmRel : ∀ {ℓ} {I : Type ℓ} {P : Poly I} (M : PolyMagma P) → PolyRel P
  -- MgmRel M {i , f} (w , α) = Path {A = OutFrame _ w}
  --   (μ M w , μ-frm M w) (f , α)


  module _ {ℓ} {I : Type ℓ} (P : Poly I) (M : PolyMagma P) (Ψ : SubInvar (MgmRel M)) where

    test-to : {i : I} {f : Op P i} → Σ (InFrame P (i , f)) (MgmRel M) → hfiber (μ M) f
    test-to ((w , .(μ-frm M w)) , idp) = w , idp

    test-from : {i : I} {f : Op P i} → hfiber (μ M) f → Σ (InFrame P (i , f)) (MgmRel M) 
    test-from (w , idp) = (w , μ-frm M w) , idp

    -- Right.  So these maps are equivalent.

    RM = MgmRel M
    PS = P // MgmRel M
    MS = SlcMgm Ψ

    -- So, here is an explicit version which does not depend on
    -- the multiplicative coherence of M.

    rigidity-type : {i : I} {f : Op P i} (pd : W PS (i , f)) → Type ℓ
    rigidity-type {i} {f} pd = Σ (W P i) (λ w → Σ (Frame P w f)
      (λ α → (g : Ops P) → Leaf PS pd g ≃ Node P (flatn (MgmRel M) pd) g))

    rigidity-sec : {i : I} {f : Op P i} (pd : W PS (i , f)) → rigidity-type pd
    rigidity-sec pd = flatn RM pd , flatn-frm RM pd , bd-frm RM pd


    rigidity-map : {i : I} {f : Op P i} (pd : W PS (i , f)) (aut : pd == pd)
      → (po : (rigidity-sec pd) == (rigidity-sec pd) [ rigidity-type ↓ aut ])
      → (j : I) (g : Op P j) (w : W P j) (α : Frame P w g) (r : (μ M w , μ-frm M w) == (g , α))
      → (n : Node PS pd ((j , g) , ((w , α) , r)))
      → r == r
    rigidity-map (lf .(_ , _)) aut po j g w α r (lift ())
    rigidity-map (nd {i , f} (((w₀ , α₀) , r₀) , κ)) aut po .i .f .w₀ .α₀ .r₀ (inl idp) =
      transport (λ x → r₀ == r₀ [ MgmRel M ↓ x ]) claim (snd= (fst= data-auto)) 

      where w₁ : W P i
            w₁ = subst P w₀ (λ g n → flatn (MgmRel M) (κ g n) , flatn-frm (MgmRel M) (κ g n))

            data-auto : ((w₀ , α₀) , r₀) , κ == ((w₀ , α₀) , r₀) , κ
            data-auto = –> (W=-equiv PS) aut

            claim : fst= (fst= data-auto) == idp
            claim = {!snd= (fst= data-auto)!}

    -- Well, so at least you have stated the strategy.

    rigidity-map (nd (((w₀ , α₀) , r₀) , κ)) aut po j g w α r (inr ((k , h) , n₀ , n₁)) =
      rigidity-map (κ (k , h) n₀) {!!} {!!} j g w α r n₁

      where

            data-auto : ((w₀ , α₀) , r₀) , κ == ((w₀ , α₀) , r₀) , κ
            data-auto = –> (W=-equiv PS) aut




  -- Umm, yeah, this is not quite enough.  You need to add the pasting
  -- diagram itself to the rigidity type.

  -- SlcMgm : ∀ {ℓ} {I : Type ℓ} {P : Poly I} {R : PolyRel P}
  --   → SubInvar R → PolyMagma (P // R)
  -- μ (SlcMgm {R = R} Ψ) pd = (flatn R pd , flatn-frm R pd) , Ψ pd
  -- μ-frm (SlcMgm {R = R} Ψ) pd = bd-frm R pd
