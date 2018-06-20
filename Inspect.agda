{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module Inspect where

  -- Used for the "inspect idiom" in proofs below
  
  data Graph {X Y : Type₀} (f : X → Y) (x : X) (y : Y) : Type₀ where
    ingraph : f x == y → Graph f x y

  inspect : {X Y : Type₀} (f : X → Y) (x : X) → Graph f x (f x)
  inspect f x = ingraph idp

  -- Needed for a lemma.

  apd↓-cst :  ∀ {i j} {A : Type i} {B C : A → Type j} (f : {a : A} → B a → C a)
    {x y : A} {p : x == y} {u : B x} {v : B y}
    → u == v [ B ↓ p ]
    → f u == f v [ C ↓ p ]
  apd↓-cst f {p = idp} idp = idp

  to-transp-↓ : ∀ {i j} {A : Type i} (P : A → Type j) {a₁ a₂ : A}
    (p : a₁ == a₂) (y : P a₂) → transport! P p y == y [ P ↓ p ]
  to-transp-↓ _ idp _ = idp

  ↓-apd-lem : ∀ {i j k} {A : Type i} {B : A → Type j} (C : (a : A) → B a → Type k)
    {f : Π A B} {x y : A} {p : x == y}
    {u : C x (f x)} {v : C y (f y)}
    → u == v [ uncurry C ↓ pair= p (apd f p) ]
    → u == v [ (λ a → C a (f a)) ↓ p ]
  ↓-apd-lem C {p = idp} idp = idp
