{-# OPTIONS --without-K --rewriting --verbose=tc.meta.eta:30 --verbose=tc.conv.term:30 --verbose=tc.lhs:80 --verbose=tc.conv.atom:50 --verbose=tc.reduce:100 --verbose=tc.reduce.fast:110 #-}

open import HoTT

module EtaTest where

  module _ (X : Type₀) (x : X) where

    silly : ⊤ → X
    silly unit = x

    -- And how does this work?
    another : (u : ⊤) → u == unit
    another u = idp

    -- Uh, yeah.  So you have to understand how this works.
    η-test : (u : ⊤) → x == silly u
    η-test u = idp
