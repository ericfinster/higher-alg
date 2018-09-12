{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Substitution
open import SubstCoh
open import Monad
open import Magma

module SetMonad where
            
  --
  --  Our definition of a set-level monad.
  --

  record SetMonad {ℓ} {I : Type ℓ} (P : Poly I) (R : PolyRel P) : Type ℓ where
    field

      sort-is-gpd : is-gpd I
      op-is-set : (i : I) → is-set (Op P i)
      arity-is-set : {i : I} (f : Op P i) → is-set (Arity P f)
      rel-is-prop : {i : I} (w :  W P i) (f : Op P i) (α : Frame P w f) → is-prop (R w f α)
      
      mag : PolyMagma P R

    MR : PolyRel P
    MR = ΣR R (MgmRef mag)

    field

      laws : {i : I} (f : Op P i) (pd : W (P // MR) (i , f))
        →  MR (flatten MR pd) f (flatten-frm MR pd)
        
  open SetMonad

  module _ {ℓ} {I : Type ℓ} {P : Poly I} (R : PolyRel P) (M : SetMonad P R)  where

    -- Derived data
    
    HomPoly : Poly (Ops P)
    HomPoly = P // MR M

    HomRel : PolyRel HomPoly
    HomRel = FlattenRel (MR M)

    HomMagma : PolyMagma HomPoly HomRel
    mult HomMagma pd = flatten (MR M) pd , flatten-frm (MR M) pd , laws M _ pd
    mult-frm HomMagma pd = bd-frame (MR M) pd
    mult-rel HomMagma pd = laws M _ pd , idp

    -- Level calculations

    W-is-set : (i : I) → is-set (W P i)
    W-is-set = W-level P (op-is-set M) 
    
    leaf-is-set : {i : I} (w : W P i) → ∀ j → is-set (Leaf P w j)
    leaf-is-set w = n-type-right-cancel (Leaf-level P (arity-is-set M) w) (sort-is-gpd M)

    param-is-set : {i : I} (f : Op P i) → ∀ j → is-set (Param P f j)
    param-is-set f = n-type-right-cancel (arity-is-set M f) (sort-is-gpd M)
    
    frame-is-set : {i : I} (w : W P i) (f : Op P i) → is-set (Frame P w f)
    frame-is-set w f = Π-level (λ i → ≃-level (leaf-is-set w i) (param-is-set f i))

    hom-sort-is-gpd : is-gpd (Ops P)
    hom-sort-is-gpd = Σ-level (sort-is-gpd M) (λ i → raise-level _ (op-is-set M i))

    hom-op-is-set : (f : Ops P) → is-set (Op HomPoly f)
    hom-op-is-set (i , f) = Σ-level (W-is-set i) (λ w →
      Σ-level (frame-is-set w f) (λ α →
      Σ-level (raise-level _ (rel-is-prop M w f α)) (λ r →
      =-preserves-level (Σ-level (op-is-set M i) (λ g →
                         Σ-level (frame-is-set w g) λ β →
                         raise-level _ (rel-is-prop M w g β))))))

    hom-arity-is-set : {f : Ops P} (pd : Op HomPoly f) → is-set (Arity HomPoly pd)
    hom-arity-is-set pd = Node-level P (arity-is-set M) (fst pd)

    -- Yeah, well, okay, it's obvious this is going to come out right
    -- even if it's a bit annoying ...
    hom-rel-is-prop : {f : Ops P} (pd : W HomPoly f) (w : Op HomPoly f)
      (α : Frame HomPoly pd w) → is-prop (HomRel pd w α)
    hom-rel-is-prop {i , f} pd (w , α , r) β = Σ-level
      (Σ-level (rel-is-prop M (flatten (MR M) pd) f (flatten-frm (MR M) pd))
        (λ r → MgmRef-level (mag M) (op-is-set M) frame-is-set
          (λ w₀ f₀ α₀ → raise-level _ (rel-is-prop M w₀ f₀ α₀))
          (flatten (MR M) pd) f (flatten-frm (MR M) pd) r))
      (λ s → has-level-apply (Σ-level {!!} {!!})
        ((flatten (MR M) pd , flatten-frm (MR M) pd , s) , bd-frame (MR M) pd)
        ((w , α , r) , β))


    -- Derived laws

    hom-laws : {f : Ops P} (pd : Op HomPoly f)
      (coh : W (HomPoly // ΣR HomRel (MgmRef HomMagma)) (f , pd)) →
        ΣR HomRel (MgmRef HomMagma)
          (flatten (ΣR HomRel (MgmRef HomMagma)) coh) pd
          (flatten-frm (ΣR HomRel (MgmRef HomMagma)) coh)
    hom-laws {i , f} (w , α , r) coh =
      (laws M f (flatten (ΣR HomRel (MgmRef HomMagma)) coh) , pair= claim {!!}) ,
      pair= claim {!!}

      where claim : (flatten (MR M) (flatten (ΣR HomRel (MgmRef HomMagma)) coh) ,
                     flatten-frm (MR M) (flatten (ΣR HomRel (MgmRef HomMagma)) coh) ,
                     laws M f (flatten (ΣR HomRel (MgmRef HomMagma)) coh))
                    == (w , α , r)
            claim = {!!}

  -- It's funny that we get it twice, but, well, okay ...
  -- So, the point should be that this all follows from globulariy
  -- as well as the assumption that the relation here is a proposition.
  -- From there, I believe the remaining holes are, as before, simply
  -- provable directly.

  -- But we will, clearly, need to check that the relation is again a proposition.

    HomMnd : SetMonad HomPoly HomRel
    sort-is-gpd HomMnd = hom-sort-is-gpd
    op-is-set HomMnd = hom-op-is-set
    arity-is-set HomMnd = hom-arity-is-set
    rel-is-prop HomMnd = hom-rel-is-prop
    mag HomMnd = HomMagma
    laws HomMnd = hom-laws

  -- Now, we want to define an OpetopicType associated to our monad
  MndType : ∀ {ℓ} {I : Type ℓ} (P : Poly I) (R : PolyRel P) (M : SetMonad P R) → OpetopicType P R
  Ref (MndType P R M) = MgmRef (mag M)
  Hom (MndType P R M) = MndType (HomPoly R M) (HomRel R M) (HomMnd R M)

  -- set-mnd-is-algebraic : ∀ {ℓ} {I : Type ℓ} {P : Poly I} {C : CartesianRel P} (M : SetMonad P C)
  --   → is-algebraic (MndType P C M)
  -- is-mult (set-mnd-is-algebraic M) = mgm-is-mult _ _ (mag M) 
  -- hom-is-alg (set-mnd-is-algebraic M) = set-mnd-is-algebraic (HomMnd _ _ M)
