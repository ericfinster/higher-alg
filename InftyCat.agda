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

    open ∞Alg Mor
    open OpType carrier

    Hom : Ob → Ob → Type₀
    Hom x y = Ops ((unit , y) , (unit , cst x))

    comp : {x y z : Ob} → Hom x y → Hom y z → Hom x z
    comp {x} {y} {z} f g = filler-of comp-niche is-alg

      where comp-niche : niche carrier ((unit , z) , unit , cst x) 
            comp-niche = box {i = unit , z} (unit , λ { unit → y }) _ 
                           (λ { unit → box (unit , λ { unit → x }) _
                           (λ { unit → dot (unit , x) })}) ,
                             λ { (inl unit) → g ;
                                 (inr (unit , inl unit)) → f ;
                                 (inr (unit , inr (unit , ()))) }

    ident : (x : Ob) → Hom x x
    ident x = filler-of id-niche is-alg

      where id-niche : niche carrier ((unit , x) , unit , cst x)
            id-niche = (dot (unit , x)) , λ { () }
            

