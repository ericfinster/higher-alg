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

  TrivRef : ∀ {ℓ} {I : Type ℓ} {P : Poly I} → PolyRel P → PolyRel P
  TrivRef R = ΣR R λ _ _ _ _ → Lift ⊤
  
  record SetMonad {ℓ} {I : Type ℓ} (P : Poly I) (R : PolyRel P) : Type ℓ where
    field

      sort-is-gpd : is-gpd I
      op-is-set : (i : I) → is-set (Op P i)
      arity-is-set : {i : I} (f : Op P i) → is-set (Arity P f)
      rel-is-prop : {i : I} (w :  W P i) (f : Op P i) (α : Frame P w f) → is-prop (R w f α)

      is-multip : is-multiplicative P R

      laws : {i : I} (f : Op P i) (pd : W (P // TrivRef R) (i , f)) 
        → (TrivRef R) (flatten (TrivRef R) pd) f (flatten-frm (TrivRef R) pd)
        
  open SetMonad

  module _ {ℓ} {I : Type ℓ} {P : Poly I} (R : PolyRel P) (M : SetMonad P R)  where

    -- Derived data

    HomPoly : Poly (Ops P)
    HomPoly = P // (TrivRef R)

    HomRel : PolyRel HomPoly
    HomRel = FlattenRel (TrivRef R)

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
      Σ-level (frame-is-set w f) (λ α → raise-level _
      (Σ-level (rel-is-prop M w f α) (λ _ → Lift-level Unit-level))))

    hom-arity-is-set : {f : Ops P} (pd : Op HomPoly f) → is-set (Arity HomPoly pd)
    hom-arity-is-set pd = Node-level P (arity-is-set M) (fst pd)

    hom-rel-is-prop : {f : Ops P} (pd : W HomPoly f) (w : Op HomPoly f)
      (α : Frame HomPoly pd w) → is-prop (HomRel pd w α)
    hom-rel-is-prop {i , f} pd (w , α , r) β = Σ-level
      (Σ-level (rel-is-prop M (flatten (TrivRef R) pd) f (flatten-frm (TrivRef R) pd)) (λ _ → Lift-level Unit-level))
      (λ s → {!!})

    -- Yeah, and this is obvious :
    -- Goal: has-level (S ⟨-2⟩)
    --       (Path ((flatten R' pd , flatten-frm R' pd , s) , bd-frame R' pd)
    --        ((w , α , r) , β))

    hom-is-multip : {f : Ops P} (pd : W HomPoly f) → is-contr (Composite HomPoly HomRel pd)
    hom-is-multip {i , f} pd = has-level-in (ctr , pth)

      where ctr : Composite HomPoly HomRel pd
            ctr = (flatten (TrivRef R) pd , flatten-frm (TrivRef R) pd , laws M f pd) ,
              bd-frame (TrivRef R) pd , laws M f pd , idp

            pth : (c : Composite HomPoly HomRel pd) → ctr == c
            pth ((._ , ._ , ._) , ._ , (m , lift tt) , idp) =
              pair= (pair= idp (pair= idp (pair=
                (prop-has-all-paths ⦃ rel-is-prop M (flatten (TrivRef R) pd) f (flatten-frm (TrivRef R) pd) ⦄
                  (fst (laws M f pd)) m) (↓-cst-in idp)))) (↓-Σ-in {!m!} {!fst (laws M f pd)!})

    -- Yeah, so again we see here that there's this lame duplication coming from how we have
    -- defined the flatten relation.  This makes things annoying...  And I feel like if you
    -- use the kind of record setup you had before, then the proof here will be idp.

    -- This should be easily polished off: the space of paths you are trying to get a pathover
    -- in is contractible.  So clearly there is a guy over it but contractibility elim.  And
    -- then just a bit of work to make the types match.  But this is going to be fine.
    
    -- Derived laws
    hom-laws : {f : Ops P} (pd : Op HomPoly f)
      → (coh : W (HomPoly // (TrivRef HomRel)) (f , pd))
      → (TrivRef HomRel) (flatten (TrivRef HomRel) coh) pd (flatten-frm (TrivRef HomRel) coh)
    hom-laws {i , f} (w , α , r) coh =
      (laws M f (flatten (TrivRef HomRel) coh) , pair= (pair= {!!} {!!}) {!!}) , lift tt

    -- Okay, nice.  And now you really are left just with globularity
    -- like you thought, and you got around the bizarre duplication.

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
  is-mult (set-mnd-is-algebraic M) w = {!!}
  hom-is-alg (set-mnd-is-algebraic {R = R} M) =
    set-mnd-is-algebraic (HomMnd R M)
