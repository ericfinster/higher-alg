{-# OPTIONS --without-K --rewriting --type-in-type #-}

open import Base
open import UniverseOne

module TargetsOnly where

  -- Okay.  I see.  In this version, trees do not carry
  -- the additional information of their source types.
  -- Rather, that information would be *calculated*.
  
  data Tree₂' : Set → Set where
    lf₂' : (A : Set) → Tree₂' A
    nd₂' : (Γ : Ctx) (A : Set) (E : Eqv (Σ↓ Γ) A)
      → (ε : (p : CtxPos Γ) → Tree₂' (CtxTyp Γ p))
      → Tree₂' A 

  src : {A : Set} → Tree₂' A → Ctx
  src = {!!}
  
  data Tree₃ : (Γ : Ctx) (A : Set) → Eqv (Σ↓ Γ) A → Set where
    lf₃ : (Γ : Ctx) (A : Set) (E : Eqv (Σ↓ Γ) A) → Tree₃ Γ A E
    nd₃ : (A : Set) (σ : Tree₂' A)
      → (E : Eqv (Σ↓ (src σ)) A)
      → {!!}
      → Tree₃ (src σ) A E
      
  -- If you had only this, would you be able to write a corresponding
  -- frame type and all that jazz?  What would a three tree be indexed by?
  -- Well, it's target would be a cell.
