{-# OPTIONS --without-K --rewriting --type-in-type #-}

open import HoTT

module wip.NPoly where

  record Poly (I : Set) : Set where
    field
      Op : I → Set
      Param : {i : I} → Op i → Set
      Typ : {i : I} {f : Op i} → Param f → I

  open Poly
  
  data W {I : Set} (P : Poly I) : I → Set where
    lf : (i : I) → W P i
    nd : {i : I} (f : Op P i) (δ : (p : Param P f) → W P (Typ P p)) → W P i

  𝕌Poly : Poly ⊤
  Op 𝕌Poly _ = Set
  Param 𝕌Poly X = X
  Typ 𝕌Poly _ = unit


  W! : {I : Set} (P : Poly I) → {i : I} → W P i → W 𝕌Poly unit
  W! P (lf i) = lf unit
  W! P (nd f δ) = nd (Param P f) (λ p → W! P (δ p))


  -- 1Poly : Set → Set
  -- 1Poly I = (X : Set) → (X → I) → I → Set

  -- data 1W {I : Set} (P : 1Poly I) : (L : Set) → (L → I) → I → Set where
  --   1lf : (i : I) → 1W P ⊤ (λ _ → i) i
  --   1nd : {i : I} {L : Set} {τ : L → I} (p : P L τ i)
  --         (δ : L → Set) (δτ : (l : L) → δ l → I)
  --         (ε : (l : L) → 1W P (δ l) (δτ l) (τ l))
  --         → 1W P (Σ L δ) (uncurry δτ) i

  -- 1Mgm : {I : Set} (P : 1Poly I) → Set
  -- 1Mgm {I} P = (X : Set) (τ : X → I) (i : I) → 1W P X τ i → P X τ i

  -- 2Poly : {I : Set} (P : 1Poly I) → Set
  -- 2Poly {I} P = (X : Set) (τ : X → I) (i : I) → 1W P X τ i → P X τ i → Set

  -- data 2W {I : Set} (P : 1Poly I) (PP : 2Poly P) : 
  --         (X : Set) (τ : X → I) (i : I)
  --         (w : 1W P X τ i) (p : P X τ i) → Set  where
  --   2lf : {L : Set} {τ : L → I} {i : I} (p : P L τ i) → 2W P PP L τ i {!!} p
          
  -- -- Right.  And here you start to get into trouble because you are going
  -- -- to have to prove all the equations and so on as you write the constructors.

  -- -- So.  This means you need a kind of version where the universe plays an
  -- -- explicit role.

  -- -- Observation: a tree in *any* polynomial gives a tree in the universe.
  -- -- Consequently, an n-tree in any polynomial should give an n-tree in the
  -- -- universe.

  -- -- Why do you say this?  Because, it means you can express the "frame"
  -- -- condition as an element of the filling type of the universe!

  -- 2Mgm : {I : Set} (P : 1Poly I) (PP : 2Poly P) → Set
  -- 2Mgm {I} P PP = (X : Set) (τ : X → I) (i : I)
  --                   (w : 1W P X τ i) (p : P X τ i)
  --                   (pd : 2W P PP X τ i w p) → PP X τ i w p

  -- 3Poly : {I : Set} {P : 1Poly I} (PP : 2Poly P) → Set
  -- 3Poly {I} {P} PP = (X : Set) (τ : X → I) (i : I)
  --                  (w : 1W P X τ i) (p : P X τ i)
  --                  (pd : 2W P PP X τ i w p) (pp : PP X τ i w p) → Set

  -- postulate

  --   3W : {I : Set} (P : 1Poly I) (PP : 2Poly P) (PPP : 3Poly PP)
  --        (X : Set) (τ : X → I) (i : I)
  --        (w : 1W P X τ i) (p : P X τ i)
  --        (ww : 2W P PP X τ i w p) (pp : PP X τ i w p) → Set

  -- -- Well, okay.  That was surprisingly simple.  Hilariously, it seems that
  -- -- we can think of a tree as itself a kind of higher relation.  Interesting.
  -- -- Perhaps you are finally seeing the kind of globularity that you always
  -- -- thought should in fact be there....
