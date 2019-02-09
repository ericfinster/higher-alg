{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import UniCat

module wip.Delta where

  open UniCat.Category

  module FstDef where

    Toset : ∀ i → Type (lsucc i)
    Toset i = Σ (hSet i) (λ A → Σ ℕ λ n → Lift (Fin n) == fst A)
  
    ord : ∀ {i} (A : Toset i) → (fst (fst A) → fst (fst A) → Type₀)
    ord (_ , (_ , p)) x y = fst (lower (<– (coe-equiv p) x)) ≤ fst (lower (<– (coe-equiv p) y))  
  
    OrdPresMap : ∀ {i} (A : Toset i) (B : Toset i) → Type i 
    OrdPresMap {_} A@(A' , (m , p)) B@(B' , (n , q)) = Σ (fst A' → fst B') (λ f → {x y : fst A'} (p : ord A x y) → ord B (f x) (f y))
  
    OrdPresMap-is-set : ∀ {i} (A : Toset i) (B : Toset i) → is-set (OrdPresMap A B)
    OrdPresMap-is-set (A , (m , p)) (B , (n , q)) = Σ-level (Π-level (λ _ → snd B)) λ f → Πi-level λ x → Πi-level λ y → Π-level λ _ → {!!}
  
    Delta : ∀ lobj → Category {lsucc lobj} {lobj}
    obj           (Delta lobj)                 = Toset lobj
    hom           (Delta lobj) A B             = OrdPresMap A B
    _●_           (Delta lobj) (g , q) (f , p) = g ∘ f , q ∘ p   
    assoc         (Delta lobj) _ _ _           = idp
    id            (Delta lobj)                 = (idf _ , idf _)
    unit-l        (Delta lobj) _               = idp
    unit-r        (Delta lobj) _               = idp
    homs-sets     (Delta lobj) A B             = OrdPresMap-is-set A B



  -- Alternative definition in terms of an explictly defined total order, don't know which one is the easiest to use
  module SndDef where

    -- FinSets as defined in HoTT-Agda except for the universe polymorphism 
    FinSet-prop : ∀ {i} → SubtypeProp (Type i) (lsucc i)
    FinSet-prop = (λ A → Trunc -1 (Σ ℕ λ n → Lift (Fin n) == A)) , λ A → Trunc-level
  
    FinSet : ∀ i → Type (lsucc i) 
    FinSet _ = Subtype FinSet-prop
  
    record TotalOrd {i} (A : FinSet i) : Type (lsucc i) where
      field
        _≤'_    : fst A → fst A → Type i
        ≤'-prop : (x y : fst A) → is-prop (x ≤' y)
        refl    : (x : fst A) → x ≤' x
        trans   : (x y z : fst A) → x ≤' y → y ≤' z → x ≤' z
        antisym : (x y : fst A) → x ≤' y → y ≤' x → y == x
        total   : (x y : fst A) → (x ≤' y) ⊔ (y ≤' x)

    open TotalOrd

    -- Order preserving maps
    OrdPresMap : ∀ {i} (A : Σ (FinSet i) TotalOrd) (B : Σ (FinSet i) TotalOrd) → Type i 
    OrdPresMap {_} (A , ordA) (B , ordB) = Σ (fst A → fst B) (λ f → {x y : fst A} → _≤'_ ordA x y → _≤'_ ordB (f x) (f y))
  
    OrdPresMap-is-set : ∀ {i} (A : Σ (FinSet i) TotalOrd) (B : Σ (FinSet i) TotalOrd) → is-set (OrdPresMap A B)
    OrdPresMap-is-set (A , ordA) (B , ordB) =
      let FinSet-is-set : ∀ {i} (A : FinSet i) → is-set (fst A)
          FinSet-is-set = {!!}
          
      in Σ-level (Π-level (λ _ → FinSet-is-set B)) (λ f → Πi-level λ x → Πi-level λ y → Π-level λ _ → raise-level _ (≤'-prop ordB (f x) (f y)))   
  
    Delta : ∀ lobj → Category {lsucc lobj} {lobj}
    obj           (Delta lobj)                 = Σ (FinSet lobj) TotalOrd
    hom           (Delta lobj) A B             = OrdPresMap A B
    _●_           (Delta lobj) (g , q) (f , p) = g ∘ f , q ∘ p   
    assoc         (Delta lobj) _ _ _           = idp
    id            (Delta lobj)                 = (idf _ , idf _)
    unit-l        (Delta lobj) _               = idp
    unit-r        (Delta lobj) _               = idp
    homs-sets     (Delta lobj) A B             = OrdPresMap-is-set A B
  

  
