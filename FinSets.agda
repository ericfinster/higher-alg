{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module FinSets where

  -- Okay, I'm going to try to make something like a "univalent universe of finite sets".

  data FinSet : Type₀ 
  El : FinSet → Type₀

  data FinSet where
    ∅ : FinSet
    S : FinSet → FinSet
    σ : (X : FinSet) (P : El X → FinSet) → FinSet

  El ∅ = ⊥
  El (S X) = ⊤ ⊔ (El X) 
  El (σ X P) = Σ (El X) (λ i → El (P i))

  -- Oh, I think I see.  You could make it a higher inductive
  -- type, right?  And you don't need successor: just 0, 1, 2.
