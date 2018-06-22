{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Poly
open import PolyMonads
open import OpetopicTypes

module InftyCat where

  ∞Cat : Type₁
  ∞Cat = Σ Type₀ (λ Ob → ∞Alg (slc (pb (id ⊤) (λ { unit → Ob }))))

  module _  (C : ∞Cat) where

    Ob = fst C
    Mor = snd C

    open OpType (fst Mor)

    -- I see, I think you should define Hom the other way ...
    Hom : Ob → Ob → Type₀
    Hom x y = Ops ((unit , y) , (unit , cst x))

    comp : {x y z : Ob} → Hom x y → Hom y z → Hom x z
    comp {x} {y} {z} f g = filler-of CompNiche (snd Mor)

      where CompNiche : Niche (fst Mor) ((unit , z) , unit , cst x) 
            CompNiche = box {i = unit , z} (unit , λ { unit → y }) _ 
                          (λ { unit → box (unit , λ { unit → x }) _
                          (λ { unit → dot (unit , x) })}) ,
                            λ { (inl unit) → g ;
                                (inr (unit , inl unit)) → f ;
                                (inr (unit , inr (unit , ()))) }

    ident : (x : Ob) → Hom x x
    ident x = filler-of IdNiche (snd Mor)

      where IdNiche : Niche (fst Mor) ((unit , x) , unit , cst x)
            IdNiche = (dot (unit , x)) , λ { () }
            

