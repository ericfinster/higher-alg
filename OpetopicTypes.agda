{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import PolyMonads

module OpetopicTypes where

  record OpType {I : Type₀} (M : Mnd I) : Type₁ where
    coinductive
    field

      Ob : I → Type₀
      Hom : OpType (slc (pb M Ob))

  open OpType
  
  -- Now, the definition will be that the space of fillers for
  -- a given niche is contractible.
  
  Niche : {I : Type₀} {M : Mnd I} (X : OpType M) → I → Type₀
  Niche {M = M} X i = ⟦ M ⟧ (Ob X) i

  Fillers : {I : Type₀} {M : Mnd I} (X : OpType M) (i : I) (n : Niche X i) → Type₀
  Fillers X i n = Σ (Ob X i) (λ x → Ob (Hom X) ((i , x) , n))

  record is-coherent {I : Type₀} {M : Mnd I} (X : OpType M) : Type₀ where
    coinductive
    field

      has-unique-fillers : {i : I} (n : Niche X i) → is-contr (Fillers X i n)
      hom-is-coherent : is-coherent (Hom X)

  open is-coherent

  -- What should it mean to be *complete*?  The notion I have in mind
  -- is that the identity structure of the type(s) coincide with the
  -- groupoid structure of the opetope.

  -- So, in order to make this precise, we will need to define the
  -- identity on an element in a coherent type

  module _ {I : Type₀} {M : Mnd I} (X : OpType M) where

    identity : {i : I} (x : Ob X i) → Ob (Hom X) ((i , x) , (η M i , λ p → transport (Ob X) (ap (τ M) (ηp-unique M i p)) x))
    identity x = {!!}



  ∞Alg : {I : Type₀} (M : Mnd I) → Type₁
  ∞Alg M = Σ (OpType M) is-coherent

  A∞-Mnd : Mnd (⊤ × ⊤)
  A∞-Mnd = slc (id ⊤)

  module A∞Spaces (X : ∞Alg A∞-Mnd) where

    X₀ : Type₀
    X₀ = Ob (fst X) (unit , unit)
    
    mult : X₀ → X₀ → X₀
    mult x y = fst (fst (has-level-apply (has-unique-fillers (snd X) mult-niche)))
    
      where mult-niche : Niche (fst X) (unit , unit)
            mult-niche = (box unit (λ _ → unit) (λ _ → box unit (λ _ → unit) (λ _ → dot unit))) ,
                         λ { (inl unit) → x ;
                             (inr (unit , inl unit)) → y ;
                             (inr (unit , inr (unit , ()))) }
