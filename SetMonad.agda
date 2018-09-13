{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Substitution
open import SubstCoh
open import Monad
open import Globularity

module SetMonad where
            
  --
  --  Our definition of a set-level monad.
  --

  TRef : ∀ {ℓ} {I : Type ℓ} {P : Poly I} (R : PolyRel P) → Refinement R
  TRef R _ _ _ _ = Lift ⊤

  infixl 50 ↑_
  
  ↑_ : ∀ {ℓ} {I : Type ℓ} {P : Poly I} → PolyRel P → PolyRel P
  ↑ R = ΣR R (TRef R)

  -- easy ...
  postulate
    ↑-is-mult : ∀ {ℓ} {I : Type ℓ} {P : Poly I} (R : PolyRel P)
      → is-multiplicative P R
      → is-multiplicative P (↑ R)

  record SetMonad {ℓ} {I : Type ℓ} (P : Poly I) (R : PolyRel P) : Type ℓ where
    field

      sort-is-gpd : is-gpd I
      op-is-set : (i : I) → is-set (Op P i)
      arity-is-set : {i : I} (f : Op P i) → is-set (Arity P f)
      rel-is-prop : {i : I} (w :  W P i) (f : Op P i) (α : Frame P w f) → is-prop (R w f α)

      is-multip : is-multiplicative P R

      laws : {i : I} (f : Op P i) (pd : W (P // ↑ R) (i , f)) 
        → (↑ R) (flatten (↑ R) pd) f (flatten-frm (↑ R) pd)
        
  open SetMonad

  module _ {ℓ} {I : Type ℓ} {P : Poly I} (R : PolyRel P) (M : SetMonad P R)  where

    -- Derived data

    HomPoly : Poly (Ops P)
    HomPoly = P // (↑ R)

    HomRel : PolyRel HomPoly
    HomRel = FlattenRel (↑ R)

    -- Level calculations

    W-is-set : (i : I) → is-set (W P i)
    W-is-set = W-level P (op-is-set M) 

    hom-sort-is-gpd : is-gpd (Ops P)
    hom-sort-is-gpd = Σ-level (sort-is-gpd M) (λ i → raise-level _ (op-is-set M i))

    hom-op-is-set : (f : Ops P) → is-set (Op HomPoly f)
    hom-op-is-set (i , f) = Σ-level (W-is-set i) (λ w →
      Σ-level (Frame-level P (sort-is-gpd M) (arity-is-set M) w f) (λ α → raise-level _
      (Σ-level (rel-is-prop M w f α) (λ _ → Lift-level Unit-level))))

    hom-arity-is-set : {f : Ops P} (pd : Op HomPoly f) → is-set (Arity HomPoly pd)
    hom-arity-is-set pd = Node-level P (arity-is-set M) (fst pd)

    hom-rel-is-prop : {f : Ops P} (pd : W HomPoly f) (w : Op HomPoly f)
      (α : Frame HomPoly pd w) → is-prop (HomRel pd w α)
    hom-rel-is-prop {i , f} pd (w , α , r) β = Σ-level
      (Σ-level (rel-is-prop M (flatten (↑ R) pd) f (flatten-frm (↑ R) pd)) (λ _ → Lift-level Unit-level))
      (λ s → has-level-apply (Σ-level (Σ-level (W-is-set i)
        (λ w₀ → Σ-level (Frame-level P (sort-is-gpd M) (arity-is-set M) w₀ f)
        (λ α₀ → raise-level _ (Σ-level (rel-is-prop M w₀ f α₀) (λ _ → Lift-level Unit-level)))))
        (λ w₁ → Frame-level (P // ↑ R) hom-sort-is-gpd hom-arity-is-set pd w₁))
         ((flatten (↑ R) pd , flatten-frm (↑ R) pd , s) , bd-frame (↑ R) pd)
         ((w , α , r) , β))

    postulate
      hom-is-multip : {f : Ops P} (pd : W HomPoly f) → is-contr (Composite HomPoly HomRel pd)
      
    -- hom-is-multip {i , f} pd = has-level-in (ctr , pth)

    --   where ctr : Composite HomPoly HomRel pd
    --         ctr = (flatten (↑ R) pd , flatten-frm (↑ R) pd , laws M f pd) ,
    --           bd-frame (↑ R) pd , laws M f pd , idp

    --         pth : (c : Composite HomPoly HomRel pd) → ctr == c
    --         pth ((._ , ._ , ._) , ._ , (m , lift tt) , idp) =
    --           pair= (pair= idp (pair= idp (pair=
    --             (prop-has-all-paths ⦃ rel-is-prop M (flatten (↑ R) pd) f (flatten-frm (↑ R) pd) ⦄
    --               (fst (laws M f pd)) m) (↓-cst-in idp)))) {!!}
    
    -- Derived laws
    hom-laws : {f : Ops P} (pd : Op HomPoly f)
      → (coh : W (HomPoly // (↑ HomRel)) (f , pd))
      → (↑ HomRel) (flatten (↑ HomRel) coh) pd (flatten-frm (↑ HomRel) coh)
    hom-laws {i , f} (w , α , r) coh = 
      (laws M f (flatten (↑ HomRel) coh) ,
        pair= (pair= (flatten-flatten R (TRef R) (TRef HomRel) w α r coh)
        (↓-Σ-in (flatten-frm-flatten R (TRef R) (TRef HomRel) w α r coh) q))
        (flatten-bd-flatten R (TRef R) (TRef HomRel) w α r coh (laws M f (flatten (↑ HomRel) coh)) q)) , lift tt

      where q : laws M f (flatten (↑ HomRel) coh) == r [ uncurry (λ a → (↑ R) a f) ↓
                  pair= (flatten-flatten R (TRef R) (TRef HomRel) w α r coh)
                  (flatten-frm-flatten R (TRef R) (TRef HomRel) w α r coh) ]
            q = prop-has-all-paths-↓ {B = uncurry (λ a → (↑ R) a f)}
                  ⦃ Σ-level (rel-is-prop M w f α) (λ _ → Lift-level Unit-level) ⦄

    HomMnd : SetMonad HomPoly HomRel
    sort-is-gpd HomMnd = hom-sort-is-gpd
    op-is-set HomMnd = hom-op-is-set
    arity-is-set HomMnd = hom-arity-is-set
    rel-is-prop HomMnd = hom-rel-is-prop
    is-multip HomMnd = hom-is-multip
    laws HomMnd = hom-laws

  -- Now, we want to define an OpetopicType associated to our monad
  MndType : ∀ {ℓ} {I : Type ℓ} (P : Poly I) (R : PolyRel P) (M : SetMonad P R) → OpetopicType P R
  Ref (MndType P R M) w f α r = Lift ⊤
  Hom (MndType P R M) = MndType (HomPoly R M) (HomRel R M) (HomMnd R M)

  set-mnd-is-algebraic : ∀ {ℓ} {I : Type ℓ} {P : Poly I} {R : PolyRel P} (M : SetMonad P R)
    → is-algebraic (MndType P R M)
  is-mult (set-mnd-is-algebraic {R = R} M) = ↑-is-mult R (is-multip M) 
  hom-is-alg (set-mnd-is-algebraic {R = R} M) =
    set-mnd-is-algebraic (HomMnd R M)
