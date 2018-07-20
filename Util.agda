{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module Util where

  -- Used for the "inspect idiom" in proofs below
  
  data Graph {X : Type₀} {Y : X → Type₀} (f : ∀ x → Y x) (x : X) (y : Y x) : Type₀ where
    ingraph : f x == y → Graph f x y

  inspect : {X : Type₀} {Y : X → Type₀} (f : ∀ x → Y x) (x : X) → Graph f x (f x)
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
    (f : Π A B) {x y : A} (p : x == y)
    {u : C x (f x)} {v : C y (f y)}
    → u == v [ uncurry C ↓ pair= p (apd f p) ]
    → u == v [ (λ a → C a (f a)) ↓ p ]
  ↓-apd-lem C f idp idp = idp

  ⊔-emap : ∀ {i i' j j'} {A : Type i} {A' : Type i'}
    → {B : Type j} {B' : Type j'}
    → A ≃ B → A' ≃ B' → A ⊔ A' ≃ B ⊔ B'
  ⊔-emap {A = A} {A' = A'} {B = B} {B' = B'} e f =
    equiv to from to-from from-to

    where to : A ⊔ A' → B ⊔ B'
          to (inl a) = inl (–> e a)
          to (inr a') = inr (–> f a')

          from : B ⊔ B' → A ⊔ A'
          from (inl b) = inl (<– e b)
          from (inr b') = inr (<– f b')

          to-from : (b : B ⊔ B') → to (from b) == b
          to-from (inl b) = <– (inl=inl-equiv (–> e (<– e b)) b) (<–-inv-r e b)
          to-from (inr b') = <– (inr=inr-equiv (–> f (<– f b')) b') (<–-inv-r f b')

          from-to : (a : A ⊔ A') → from (to a) == a
          from-to (inl a) = <– (inl=inl-equiv (<– e (–> e a)) a) (<–-inv-l e a)
          from-to (inr a') = <– (inr=inr-equiv (<– f (–> f a')) a') (<–-inv-l f a')
