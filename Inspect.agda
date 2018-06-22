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


  private
    htpy-natural : ∀ {i j} {A : Type i} {B : Type j} {x y : A} {f g : A → B}
      (p : ∀ x → (f x == g x)) (q : x == y) → ap f q ∙ p y == p x ∙ ap g q
    htpy-natural p idp = ! (∙-unit-r _)

    htpy-natural-app=idf : ∀ {i} {A : Type i} {f : A → A}
      (p : ∀ (x : A) → f x == x) → (∀ x → ap f (p x) == p (f x))
    htpy-natural-app=idf {f = f} p x = anti-whisker-right (p x) $
      htpy-natural p (p x) ∙ ap (p (f x) ∙_) (ap-idf (p x))

  module _ {i} {j} {A : Type i} {B : Type j} where

    record is-equiv' (f : A → B) : Type (lmax i j)
      where
      field
        g : B → A
        f-g : (b : B) → f (g b) == b
        g-f : (a : A) → g (f a) == a
        adj : (a : A) → ap f (g-f a) == f-g (f a)

      adj' : (b : B) → ap g (f-g b) == g-f (g b)
      adj' b = anti-whisker-left (ap g (f-g (f (g b)))) $ ! $
        ap g (f-g (f (g b))) ∙ g-f (g b)
          =⟨ ! $ htpy-natural-app=idf f-g b |in-ctx (λ p → ap g p ∙ g-f (g b)) ⟩
        ap g (ap (f ∘ g) (f-g b)) ∙ g-f (g b)
          =⟨ ! $ ap-∘ g (f ∘ g) (f-g b) |in-ctx (λ p → p ∙ g-f (g b)) ⟩
        ap (g ∘ f ∘ g) (f-g b) ∙ g-f (g b)
          =⟨ htpy-natural (g-f ∘ g) (f-g b) ⟩
        g-f (g (f (g b))) ∙ ap g (f-g b)
          =⟨ ! $ htpy-natural-app=idf g-f (g b) |in-ctx (λ p → p ∙ ap g (f-g b)) ⟩
        ap (g ∘ f) (g-f (g b)) ∙ ap g (f-g b)
          =⟨ ap-∘ g f (g-f (g b)) |in-ctx (λ p → p ∙ ap g (f-g b)) ⟩
        ap g (ap f (g-f (g b))) ∙ ap g (f-g b)
          =⟨ adj (g b) |in-ctx (λ p → ap g p ∙ ap g (f-g b)) ⟩
        ap g (f-g (f (g b))) ∙ ap g (f-g b)
          =∎

    is-eq' : (f : A → B)
      (g : B → A) (f-g : (b : B) → f (g b) == b)
      (g-f : (a : A) → g (f a) == a) → is-equiv' f
    is-eq' f g f-g g-f =
     record {g = g; f-g = f-g'; g-f = g-f; adj = adj} where
       f-g' : (b : B) → f (g b) == b
       f-g' b = ! (ap (f ∘ g) (f-g b)) ∙ ap f (g-f (g b)) ∙ f-g b

       adj : (a : A) → ap f (g-f a) == f-g' (f a)
       adj a =
        ap f (g-f a)
          =⟨ ! (!-inv-l (ap (f ∘ g) (f-g (f a)))) |in-ctx (λ q → q ∙ ap f (g-f a)) ⟩
        (! (ap (f ∘ g) (f-g (f a))) ∙ ap (f ∘ g) (f-g (f a))) ∙ ap f (g-f a)
          =⟨ ∙-assoc (! (ap (f ∘ g) (f-g (f a)))) (ap (f ∘ g) (f-g (f a))) _ ⟩
        ! (ap (f ∘ g) (f-g (f a))) ∙ ap (f ∘ g) (f-g (f a)) ∙ ap f (g-f a)
          =⟨ lemma |in-ctx (λ q → ! (ap (f ∘ g) (f-g (f a))) ∙ q) ⟩
        ! (ap (f ∘ g) (f-g (f a))) ∙ ap f (g-f (g (f a))) ∙ f-g (f a) =∎
        where
        lemma : ap (f ∘ g) (f-g (f a)) ∙ ap f (g-f a)
             == ap f (g-f (g (f a))) ∙ f-g (f a)
        lemma =
          ap (f ∘ g) (f-g (f a)) ∙ ap f (g-f a)
            =⟨ htpy-natural-app=idf f-g (f a) |in-ctx (λ q → q ∙ ap f (g-f a)) ⟩
          f-g (f (g (f a))) ∙ ap f (g-f a)
            =⟨ ! (ap-idf (ap f (g-f a))) |in-ctx (λ q → f-g (f (g (f a))) ∙ q) ⟩
          f-g (f (g (f a))) ∙ ap (idf B) (ap f (g-f a))
            =⟨ ! (htpy-natural f-g (ap f (g-f a))) ⟩
          ap (f ∘ g) (ap f (g-f a)) ∙ f-g (f a)
            =⟨ ap-∘ f g (ap f (g-f a)) |in-ctx (λ q → q ∙ f-g (f a)) ⟩
          ap f (ap g (ap f (g-f a))) ∙ f-g (f a)
            =⟨ ∘-ap g f (g-f a) ∙ htpy-natural-app=idf g-f a
               |in-ctx (λ q → ap f q ∙ f-g (f a)) ⟩
          ap f (g-f (g (f a))) ∙ f-g (f a) =∎

  infix 30 _≃'_

  _≃'_ : ∀ {i j} (A : Type i) (B : Type j) → Type (lmax i j)
  A ≃' B = Σ (A → B) is-equiv'

  module _ {i} {j} {A : Type i} {B : Type j} where

    equiv' : (f : A → B) (g : B → A) (f-g : (b : B) → f (g b) == b)
            (g-f : (a : A) → g (f a) == a) → A ≃' B
    equiv' f g f-g g-f = (f , is-eq' f g f-g g-f)
