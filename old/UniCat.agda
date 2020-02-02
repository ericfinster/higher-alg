{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module UniCat where

  -- Definition of a pre-category
  record PreCategory lobj larrow : Type (lsucc (lmax lobj larrow)) where
    infixl 40 _●_
    field
      obj       : Type lobj
      hom       : obj → obj → Type larrow
      _●_       : {x y z : obj} (g : hom y z) (f : hom x y) → hom x z
      assoc     : {x y z t : obj} (h : hom z t) (g : hom y z) (f : hom x y) → (h ● g) ● f == h ● (g ● f)
      id        : {x : obj} → hom x x
      unit-l    : {x y : obj} (f : hom x y) → id ● f == f
      unit-r    : {x y : obj} (f : hom x y) → f ● id == f
      homs-sets : (x y : obj) → is-set (hom x y)

  module _ {lobj larrow} {P : PreCategory lobj larrow} where

    open PreCategory P

    -- Definition of an equivalence in a category
    record is-cat-equiv {x y : obj} (f : hom x y) : Type larrow where
      constructor mk-cat-equiv
      field
        g : hom y x
        f-g : f ● g == id
        g-f : g ● f == id

    Σ-is-cat-equiv : {x y : obj} (f : hom x y) → Σ (hom y x) (λ g → (f ● g == id) × (g ● f == id)) ≃ is-cat-equiv f
    Σ-is-cat-equiv f = equiv (λ { (g , f-g , g-f) → mk-cat-equiv g f-g g-f }) (λ { (mk-cat-equiv g f-g g-f) → (g , f-g , g-f) }) (λ _ → idp) λ _ → idp
 
    _≊_ : (x y : obj) → Type larrow
    _≊_ x y = Σ (hom x y) (λ f → is-cat-equiv f)

    ≊-is-set : (x y : obj) → is-set (x ≊ y)
    ≊-is-set x y =
      let Σ-is-cat-equiv-is-set _ = Σ-level (homs-sets _ _) λ _ → Σ-level (=-preserves-level (homs-sets _ _)) λ _ → (=-preserves-level (homs-sets _ _))
      in Σ-level (homs-sets _ _) λ f → equiv-preserves-level (Σ-is-cat-equiv _) ⦃ (Σ-is-cat-equiv-is-set f) ⦄

    id-to-iso : (x y : obj) → x == y → x ≊ y
    id-to-iso x y idp = id , mk-cat-equiv id (unit-l _) (unit-l _) 

  open PreCategory

  record Category lobj larrow : Type (lsucc (lmax lobj larrow)) where
    field
      precat    : PreCategory lobj larrow
      univalent : (x y : obj precat) → is-equiv (id-to-iso {P = precat} x y)
    open PreCategory precat public

  module _ {lobj lobj' larrow larrow'} (Cat : Category lobj larrow) (Cat' : Category lobj' larrow') where

    open Category Cat renaming (precat to C)
    open Category Cat' renaming (precat to C')   

    record Functor : Type (lsucc (lmax (lmax lobj lobj') (lmax larrow larrow'))) where
      field
        fobj  : obj C → obj C'
        farr  : {x y : obj C} → hom C x y → hom C' (fobj x) (fobj y)
        fcomp : {x y z : obj C} (f : hom C x y) (g : hom C y z) → farr (_●_ C g f) == _●_ C' (farr g) (farr f) 
        fid   : {x : obj C} → farr (id C {x = x}) == id C' {x = fobj x}

    open Functor

    record NatTrans (F F' : Functor) : Type (lsucc (lmax (lmax lobj lobj') (lmax larrow larrow'))) where
      field
        η        : (x : obj C) → hom C' (fobj F x) (fobj F' x)
        η-commut : {x y : obj C} (f : hom C x y) → _●_ C' (η y) (farr F f)  == _●_ C' (farr F' f) (η x)

    open NatTrans
