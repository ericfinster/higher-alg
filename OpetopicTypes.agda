{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import PolyMonads

module OpetopicTypes where

  record OpType {I : Type₀} (M : Mnd I) : Type₁ where
    coinductive
    field

      Ops : I → Type₀
      Rels : OpType (slc (pb M Ops))

  open OpType
  
  -- Now, the definition will be that the space of fillers for
  -- a given niche is contractible.
  
  Niche : {I : Type₀} {M : Mnd I} (X : OpType M) → I → Type₀
  Niche {M = M} X i = ⟪ M ⟫ (Ops X) i

  Fillers : {I : Type₀} {M : Mnd I} (X : OpType M) (i : I) (n : Niche X i) → Type₀
  Fillers X i n = Σ (Ops X i) (λ x → Ops (Rels X) ((i , x) , n))

  record is-coherent {I : Type₀} {M : Mnd I} (X : OpType M) : Type₀ where
    coinductive
    field

      has-unique-fillers : {i : I} (n : Niche X i) → is-contr (Fillers X i n)
      hom-is-coherent : is-coherent (Rels X)

  open is-coherent

  filler-of : {I : Type₀} {M : Mnd I} {X : OpType M} {i : I}
              (n : Niche X i) (is-coh : is-coherent X) → Ops X i
  filler-of n is-coh = fst (fst (has-level-apply (has-unique-fillers is-coh n)))              

  pth-to-id-cell : {I : Type₀} {M : Mnd I} (X : OpType M) (is-coh : is-coherent X)
                   {i : I} (x y : Ops X i) (p : x == y) → 
                   Ops (Rels X) ((i , x) , (η M i , λ p → transport (Ops X) (ap (τ M) (ηρ-η M i p)) y))
  pth-to-id-cell {M = M} X is-coh {i} x .x idp = filler-of id-niche (hom-is-coherent is-coh)

    where id-niche : Niche (Rels X) (((i , x) , (η M i , λ p → transport (Ops X) (ap (τ M) (ηρ-η M i p)) x)))
          id-niche = dot (i , x) , λ { () }

  record is-complete {I : Type₀} {M : Mnd I} (X : OpType M) (is-coh : is-coherent X) : Type₀ where
    coinductive
    field

      pth-to-id-equiv : {i : I} (x y : Ops X i) → is-equiv (pth-to-id-cell X is-coh x y)
      hom-is-complete : is-complete (Rels X) (hom-is-coherent is-coh)

  ∞Alg : {I : Type₀} (M : Mnd I) → Type₁
  ∞Alg M = Σ (OpType M) is-coherent

