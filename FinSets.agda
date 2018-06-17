{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module FinSets where

  -- Okay, I'm going to try to make something like a "univalent universe of finite sets".

  data FinSet : Type₀ 
  El : FinSet → Type₀

  data FinSet where
    ∅ : FinSet
    σ : (X : FinSet) (P : El X → FinSet) → FinSet

  El ∅ = ⊥
  El (σ X P) = Σ (El X) (λ i → El (P i))

  -- Oh, I think I see.  You could make it a higher inductive
  -- type, right?  And you don't need successor: just 0....

  -- Right, so um, idea: have a universe of finite sets whose
  -- constructors mirror the way places should be constructed
  -- in the slice.

  -- Indeed.  Or something like this ....
  -- Yeah, okay.  There is some kind of formula like that....
