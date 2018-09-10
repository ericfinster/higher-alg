{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Substitution
open import SubstCoh
open import Monad

module SetMonad where

  record PolyMagma {ℓ} {I : Type ℓ} (P : Poly I) (C : CartesianRel P) : Type ℓ where
    field

      mult : {i : I} (w : W P i) → Op P i
      mult-rel : {i : I} (w : W P i) → fst C w (mult w)

  open PolyMagma

  MgmExt : ∀ {ℓ} {I : Type ℓ} (P : Poly I) (C : CartesianRel P)
    → (M : PolyMagma P C) → Refinement C
  MgmExt P C M {i} w f r = (mult M w , mult-rel M w) == (f , r)

  mgm-is-mult : ∀ {ℓ} {I : Type ℓ} (P : Poly I) (C : CartesianRel P)
    → (M : PolyMagma P C)
    → is-multiplicative P (ΣRef C (MgmExt P C M))
  mgm-is-mult P C M w = has-level-in (ctr , pth)

    where ctr : Composite P (ΣRef C (MgmExt P C M)) w
          ctr = mult M w , mult-rel M w , idp

          pth : (c : Composite P (ΣRef C (MgmExt P C M)) w) → ctr == c
          pth (._ , ._ , idp) = idp

  --
  --  Our definition of a set-level monad.
  --
  
  record SetMonad {ℓ} {I : Type ℓ} (P : Poly I) (C : CartesianRel P) : Type ℓ where
    field

      sort-is-gpd : is-gpd I
      rel-is-set : {i : I} (w :  W P i) (f : Op P i) → is-set (fst C w f)
      ops-is-set : (i : I) → is-set (Op P i)
      arity-is-set : {i : I} (f : Op P i) → is-set (Arity P f)

      mag : PolyMagma P C

      laws : {i : I} (f : Op P i) (pd : W (P // fst (ΣRef C (MgmExt P C mag))) (i , f))
        → fst (ΣRef C (MgmExt P C mag)) (flatten (ΣRef C (MgmExt P C mag)) pd) f
        
  open SetMonad

  module _ {ℓ} {I : Type ℓ} (P : Poly I) (C : CartesianRel P) (M : SetMonad P C)  where

    -- Idea is clear: from a set monad, pass to the canonical fillers given
    -- by the identity types and show that this is again a set monad.
    private
      R = ΣRef C (MgmExt P C (mag M))

    HomPoly : Poly (Ops P)
    HomPoly = P // fst R

    hom-op-is-set : (f : Ops P) → is-set (Op HomPoly f)
    hom-op-is-set (_ , f) = Σ-level (W-level P (ops-is-set M) _)
      (λ w → Σ-level (rel-is-set M w f) (λ r → =-preserves-level (Σ-level (ops-is-set M _)
      (λ f → rel-is-set M w f))))

    hom-mult : {i : I} (f : Op P i) → W HomPoly (i , f) → Op HomPoly (i , f)
    hom-mult f w = flatten R w , laws M f w 

    hom-mult-rel : {i : I} (f : Op P i)
      → (w : W HomPoly (i , f))
      → fst (FlattenRel R) w (hom-mult f w) 
    hom-mult-rel f w = idp
    
    HomMult : PolyMagma HomPoly (FlattenRel R)
    mult HomMult {i , f} = hom-mult f
    mult-rel HomMult {i , f} = hom-mult-rel f

    hom-laws : {f : Ops P} (pd : Op HomPoly f)
      → (coh : W (HomPoly // fst (ΣRef (FlattenRel R) (MgmExt HomPoly (FlattenRel R) HomMult))) (f , pd))
      → fst (ΣRef (FlattenRel R) (MgmExt HomPoly (FlattenRel R) HomMult))
            (flatten (ΣRef (FlattenRel R) (MgmExt HomPoly (FlattenRel R) HomMult)) coh) pd
    hom-laws (w , (r , e)) (lf i) =
      substitute-unit R w , (pair= (pair= (substitute-unit R w) {!!})
        (prop-has-all-paths-↓ {B = (fst (FlattenRel R) (nd ((w , r , e) , (λ j p → lf j))))}
          ⦃ has-level-apply ((W-level P (ops-is-set M) _)) (substitute R w (λ j p → lf j)) w ⦄))
      
    hom-laws ._ (nd ((w , ._ , idp) , κ)) = {!!} , {!!}

    -- prop-has-all-paths-↓ : {x y : A} {p : x == y} {u : B x} {v : B y}
    --   {{_ : is-prop (B y)}} → u == v [ B ↓ p ]
    -- prop-has-all-paths-↓ {p = idp} = prop-has-all-paths _ _

  -- FlattenRel : CartesianRel (P // R)
  -- FlattenRel = (λ pd wr → flatten pd == fst wr) ,
  --              (λ { pd (._ , r) idp → bd-frame pd })


    HomMnd : SetMonad HomPoly (FlattenRel R)
    sort-is-gpd HomMnd = Σ-level (sort-is-gpd M) (λ i → raise-level _ (ops-is-set M i))
    rel-is-set HomMnd w f = =-preserves-level (W-level P (ops-is-set M) _)
    ops-is-set HomMnd = hom-op-is-set
    arity-is-set HomMnd (w , _) = Node-level P (arity-is-set M) w
    mag HomMnd = HomMult
    laws HomMnd = hom-laws

  -- Now, we want to define an OpetopicType associated to our monad
  MndType : ∀ {ℓ} {I : Type ℓ} (P : Poly I) (C : CartesianRel P) (M : SetMonad P C) → OpetopicType P C
  OpetopicType.Ref (MndType P C M) = MgmExt P C (mag M) 
  OpetopicType.Hom (MndType P C M) = MndType (HomPoly P C M) (FlattenRel (ΣRef C (MgmExt P C (mag M)))) (HomMnd P C M)

  set-mnd-is-algebraic : ∀ {ℓ} {I : Type ℓ} {P : Poly I} {C : CartesianRel P} (M : SetMonad P C)
    → is-algebraic (MndType P C M)
  is-mult (set-mnd-is-algebraic M) = mgm-is-mult _ _ (mag M) 
  hom-is-alg (set-mnd-is-algebraic M) = set-mnd-is-algebraic (HomMnd _ _ M)
