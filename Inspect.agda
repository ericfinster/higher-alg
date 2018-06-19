{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module Inspect where

  -- Used for the "inspect idiom" in proofs below
  
  data Graph {X Y : Type₀} (f : X → Y) (x : X) (y : Y) : Type₀ where
    ingraph : f x == y → Graph f x y

  inspect : {X Y : Type₀} (f : X → Y) (x : X) → Graph f x (f x)
  inspect f x = ingraph idp
