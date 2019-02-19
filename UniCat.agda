{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module UniCat where

  -- Definition of a pre-category
  record Category {lobj larrow} : Type (lsucc (lmax lobj larrow)) where
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

  open Category

  -- Definition of an equivalence in a category
  record CatEquiv {lobj larrow} {C : Category {lobj} {larrow}} {x y : obj C} (f : hom C x y) : Type larrow where
    field
      g : hom C y x
      f-g : _●_ C f g == id C
      g-f : _●_ C g f == id C
 
  _≊_ : ∀ {lobj} {larrow} {C : Category {lobj} {larrow}} (x y : obj C) → Type larrow
  _≊_ {C = C} x y = Σ (hom C x y) (λ f → CatEquiv {C = C} f)

  -- -- Turning pre-categories into categories  
  -- postulate
  --   unival : ∀ {lobj} {larrow} {C : Category {lobj} {larrow}} {x y : obj C} → (_≊_ {C = C} x y) ≃ (x == y)

  id-to-equiv : ∀ {lobj} {larrow} {C : Category {lobj} {larrow}} {x y : obj C} → (x == y) → _≊_ {C = C} x y
  id-to-equiv {C = C} {x = x} idp = id C {x} , record { g = id C {x} ; f-g = {!!} ; g-f = {!!} }

  record UniCat : =============
    field
      C : cat
      is-univ : is-equiv id-to-equiv.

  record Functor {lobj lobj' larrow larrow'} (C : Category {lobj} {larrow}) (C' : Category {lobj'} {larrow'})  : Type (lsucc (lmax (lmax lobj lobj') (lmax larrow larrow'))) where
    field
      fobj  : obj C → obj C'
      farr  : {x y : obj C} → hom C x y → hom C' (fobj x) (fobj y)
      fcomp : {x y z : obj C} (f : hom C x y) (g : hom C y z) → farr (_●_ C g f) == _●_ C' (farr g) (farr f) 
      fid   : {x : obj C} → farr (id C {x = x}) == id C' {x = fobj x}

  open Functor

  record NatTrans
    {lobj} {lobj'} {larrow} {larrow'}
    {C : Category {lobj} {larrow}}
    {C' : Category {lobj'} {larrow'}}
    (F F' : Functor C C')
    : Type (lsucc (lmax (lmax lobj lobj') (lmax larrow larrow'))) where
    field
      η        : (x : obj C) → hom C' (fobj F x) (fobj F' x)
      η-commut : {x y : obj C} (f : hom C x y) → _●_ C' (η y) (farr F f)  == _●_ C' (farr F' f) (η x)

  open NatTrans
