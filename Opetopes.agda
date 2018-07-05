{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import StrictPoly

module Opetopes where
  
  MndSeq : ℕ → Mnd lzero
  MndSeq O = id ⊤ 
  MndSeq (S n) = slc (MndSeq n) 

  Opetope : ℕ → Set₀
  Opetope n = Idx (MndSeq n)

  obj : Opetope 0
  obj = unit

  arr : Opetope 1
  arr = unit , unit

  boucle : Opetope 2
  boucle = (unit , unit) , (dot unit)

  glob : Opetope 2
  glob = (unit , unit) , (box unit unit (cst unit) (cst (dot unit)))

  glob₃ : Opetope 3
  glob₃ = glob , box (unit , unit) (snd glob)
    (λ { (inl unit) → box unit unit (cst unit) (cst (dot unit)) ;
         (inr (unit , ())) })
    λ { (inl unit) → dot (unit , unit) ;
        (inr (unit , ())) }

  drop : Opetope 3
  drop = ((unit , unit) , (box unit unit (cst unit) (cst (dot unit)))) , dot (unit , unit)

  two-horns : Opetope 3
  two-horns = ((unit , unit) , box unit unit (cst unit) (cst (box unit unit (cst unit) (cst (dot unit))))) ,
    box (unit , unit) (box unit unit (cst unit) (cst (box unit unit (cst unit) (cst (dot unit)))))
      (λ { (inl unit) → box unit unit (cst unit) (cst (dot unit)) ;
           (inr (unit , inl x)) → box unit unit (cst unit) (cst (dot unit)) ;
           (inr (unit , inr (unit , ()))) })
      (λ { (inl unit) → snd glob₃ ;
           (inr (unit , inl x)) → snd glob₃ ;
           (inr (unit , inr (unit , ()))) })

  glob-on-simplex : Opetope 3
  glob-on-simplex = ((unit , unit) , box unit unit (cst unit) (cst (box unit unit (cst unit) (cst (dot unit))))) ,
    box (unit , unit) (box unit unit (cst unit) (cst (box unit unit (cst unit) (cst (dot unit)))))
      (λ { (inl unit) → box unit unit (cst unit) (cst (dot unit)) ;
           (inr (unit , inl x)) → box unit unit (cst unit) (cst (dot unit)) ;
           (inr (unit , inr (unit , ()))) })
      (λ { (inl unit) → dot (unit , unit) ;
           (inr (unit , inl x)) → dot (unit , unit) ;
           (inr (unit , inr (unit , ()))) })
