{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Poly
open import PolyMonads
open import OpetopicTypes

module InftyCat where

  -- Right, this should be an ∞PreCat .....
  -- Below you add the completeness ...
  ∞Cat : Type₁
  ∞Cat = Σ Type₀ (λ Ob → ∞Alg (slc (pb (id ⊤) (λ { unit → Ob }))))

  module _ (C : ∞Cat) where

    Ob = fst C
    Alg = snd C
    Mor = carrier Alg

    Hom : Ob → Ob → Type₀
    Hom x y = Ops Mor ((unit , y) , (unit , cst x))

    comp-niche : {x y z : Ob} → Hom y z → Hom x y →  niche Mor ((unit , z) , unit , cst x)
    comp-niche {x} {y} {z} f g = box {i = unit , z} (unit , λ { unit → y }) (λ { unit → unit , λ { unit → x }})
                                   (λ { unit → box {i = unit , y} (unit , λ { unit → x }) (λ { unit → unit , λ { unit → x }})
                                   (λ { unit → dot (unit , x) })}) ,
                                     λ { (inl unit) → f ;
                                         (inr (unit , inl unit)) → g ;
                                         (inr (unit , inr (unit , ()))) }

    -- The type of witnesses that f ∘ g = h 
    is-comp : {x y z : Ob} → Hom y z → Hom x y → Hom x z → Type₀
    is-comp {x} {y} {z} f g h = Ops (Rels Mor) ((((unit , z) , unit , cst x) , h) ,
                                                 (comp-niche f g))

    comp : {x y z : Ob} → Hom y z → Hom x y → Hom x z
    comp f g = filler-of (comp-niche f g) (is-alg Alg) 

    comp-is-comp : {x y z : Ob} (f : Hom y z) (g : Hom x y) → 
                   is-comp f g (comp f g)
    comp-is-comp f g = witness-of (comp-niche f g) (is-alg Alg)                   

    id-niche : (x : Ob) → niche Mor ((unit , x) , unit , cst x)
    id-niche x = (dot (unit , x)) , λ { () }

    ident : (x : Ob) → Hom x x
    ident x = filler-of (id-niche x) (is-alg Alg)

    -- Idea is obvious: draw the 2-pasting diagram with two loops
    -- and the witness for the identity composed with itself.
    -- It's composite is a filler for the empty niche.  Since the
    -- space of fillers is contractible, it is equal to the identity.
    -- End of proof.
    id-comp-id : (x : Ob) → is-comp (ident x) (ident x) (ident x)
    id-comp-id x = {!!}

      -- where bubble-niche : niche (Rels Mor) ((((unit , x) , unit , cst x) , comp (ident x) (ident x)) ,
      --                                         (dot (unit , x)) , λ { () })
      --       bubble-niche = (box {i = ((unit , x) , (unit , (cst x))) , (comp (ident x) (ident x)) }
      --                       (comp-niche (ident x) (ident x)) {!!}
      --                        (λ { (inl unit) → box {i = ((unit , x) , ((unit , cst x))) , (ident x)} (id-niche x) _ (λ { () }) ;               --  The first loop
      --                             (inr (unit , inl unit)) → box {i = ((unit , x) , ((unit , cst x))) , (ident x)} (id-niche x) _ (λ { () }) ;  --  The second loop
      --                             (inr (unit , inr (unit , ()))) })) ,


      --         λ { p → {!p!} } -- Here go the decorations by witnesses!

    record is-h-equiv {x y : Ob} (f : Hom x y) : Type₀ where
      field
        g₀ : Hom y x
        g₀-inv : is-comp f g₀ (ident y)
        g₁ : Hom y x
        g₁-inv : is-comp g₁ f (ident x)

    h-equiv : (x y : Ob) → Type₀
    h-equiv x y = Σ (Hom x y) (λ f → is-h-equiv f)




    -- unit-left-niche : {x y : Ob} (f : Hom x y) → niche Rels
    --   ((((unit , y) , (unit , cst x)) , f) ,
    --   (η-slc (pb (id ⊤) (λ { unit → fst C })) ((unit , y) , unit , cst x)) ,
    --   λ { (inl unit) → f ; (inr (_ , ())) })
    -- unit-left-niche {x} {y} f =
    --   (box ((box {i = unit , y} (unit , cst x) _ (λ { unit → box (unit , cst x) _ (λ { unit → dot (unit , x) }) })) ,
    --     λ { (inl unit) → f ;
    --         (inr (unit , inl unit)) → ident x ;
    --         (inr (unit , inr (unit , ()))) })
    --    {!!} {!!}) , {!!}



    
