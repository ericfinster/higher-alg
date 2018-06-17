{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module PolyMonad2 where

  data Mnd : Type₀ → Type₁

  γ : {I : Type₀} (M : Mnd I) → I → Type₀

  -- η : {I : Type₀} (M : Mnd I) (X : I → Type₀) (i : I) → X i → ⟦ M ⟧ X i
  -- μ : {I : Type₀} (M : Mnd I) (X : I → Type₀) (i : I) → ⟦ M ⟧ (⟦ M ⟧ X) i → ⟦ M ⟧ X i 

  postulate

    -- The type of decorations
    π : {I : Type₀} (M : Mnd I) {i : I} (c : γ M i) (X : I → Type₀) → Type₀
  
  η : {I : Type₀} (M : Mnd I) → (i : I) → γ M i
  μ : {I : Type₀} (M : Mnd I) {i : I} (c : γ M i) (δ : π M c (γ M)) → γ M i

  -- Now, the idea is to give "introduction rules" for decorations of
  -- these two kinds of constructors ...

  -- Yeah, but you have to be able to evaluate, right?  And then you need
  -- the places back?  Ah, I see, so I guess this is what bind gives you ...
  
  η-intro : {I : Type₀} (M : Mnd I) (i : I) (X : I → Type₀) (x : X i) → π M (η M i) X
  -- μ-intro : {I : Type₀} (M : Mnd I) (i : I) (X : I → Type₀)


  data Mnd where

  γ = {!!}

  η = {!!}
  μ = {!!}

  η-intro = {!!}
