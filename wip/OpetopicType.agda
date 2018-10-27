{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Substitution
open import SubstCoh
open import Globularity

module OpetopicType where

  -- We think of R as an "admissibility relation"
  record OpetopicType {ℓ} {I : Type ℓ} (P : Poly I) (R : PolyRel P) : Type (lsucc ℓ) where
    coinductive
    field
    
      Ref : Refinement R
      Hom : OpetopicType (P // ΣR R Ref) (FlattenRel (ΣR R Ref))

  open OpetopicType public

  -- The trivial refinement
  TRef : ∀ {ℓ} {I : Type ℓ} {P : Poly I} (R : PolyRel P) → Refinement R
  TRef R _ _ _ _ = Lift ⊤

  infixl 50 ↑_
  
  ↑_ : ∀ {ℓ} {I : Type ℓ} {P : Poly I} → PolyRel P → PolyRel P
  ↑ R = ΣR R (TRef R)

  TerminalType : ∀ {ℓ} {I : Type ℓ} (P : Poly I) (R : PolyRel P) → OpetopicType P R
  Ref (TerminalType P R) = TRef R
  Hom (TerminalType P R) = TerminalType (P // ↑ R) (FlattenRel (↑ R))

  -- This works generically for any two successive refinements
  module _ {ℓ} {I : Type ℓ} (P : Poly I) (R : PolyRel P)
    (X : Refinement R) (Y : Refinement (FlattenRel (ΣR R X))) where

    private
      R₀ = ΣR R X
      R₁ = ΣR (FlattenRel R₀) Y

    Coherence : {i : I} {f : Op P i} (pd : W (P // R₀) (i , f)) → Type ℓ
    Coherence {i} {f} pd = Σ (R (flatten R₀ pd) f (flatten-frm R₀ pd)) (λ r₀ →
      Σ (X (flatten R₀ pd) f (flatten-frm R₀ pd) r₀) (λ s₀ →
         Y pd (flatten R₀ pd , flatten-frm R₀ pd , r₀ , s₀)
              (bd-frame R₀ pd) ((r₀ , s₀) , idp)))  

    to : {i : I} {f : Op P i} (pd : W (P // R₀) (i , f))
      → Composite (P // R₀) R₁ pd → Coherence pd
    to pd ((._ , ._ , r₀ , s₀) , ._ , ((.r₀ , .s₀) , idp) , s₁) = r₀ , s₀ , s₁

    from : {i : I} {f : Op P i} (pd : W (P // R₀) (i , f))
      → Coherence pd → Composite (P // R₀) R₁ pd 
    from pd (r₀ , s₀ , s₁) = (flatten R₀ pd , flatten-frm R₀ pd , r₀ , s₀) ,
                             (bd-frame R₀ pd) , ((r₀ , s₀) , idp) , s₁

    to-from : {i : I} {f : Op P i} (pd : W (P // R₀) (i , f))
      → (coh : Coherence pd) → to pd (from pd coh) == coh
    to-from pd (r₀ , s₀ , s₁) = idp

    from-to : {i : I} {f : Op P i} (pd : W (P // R₀) (i , f))
      → (cmp : Composite (P // R₀) R₁ pd) → from pd (to pd cmp) == cmp
    from-to pd ((._ , ._ , r₀ , s₀) , ._ , ((.r₀ , .s₀) , idp) , s₁) = idp

    comp-to-coh-eqv : {i : I} {f : Op P i} (pd : W (P // R₀) (i , f))
      → Composite (P // R₀) R₁ pd ≃ Coherence pd
    comp-to-coh-eqv pd = equiv (to pd) (from pd) (to-from pd) (from-to pd)

