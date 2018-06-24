{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module 1Cat where

  record 1Cat : Type₁ where
    field
      Ob₁ : Type₀
      Hom₁ : Ob₁ → Ob₁ → Type₀
      Hom-is-set : {x y : Ob₁} → is-set (Hom₁ x y)

      id₁ : (x : Ob₁) → Hom₁ x x
      comp₁ : {x y z : Ob₁} → Hom₁ x y → Hom₁ y z → Hom₁ x z

      unit-r₁ : {x y : Ob₁} (f : Hom₁ x y) → comp₁ f (id₁ y) == f
      unit-l₁ : {x y : Ob₁} (f : Hom₁ x y) → comp₁ (id₁ x) f == f
      assoc₁ : {x y z w : Ob₁} (f : Hom₁ x y) (g : Hom₁ y z) (h : Hom₁ z w) →
               comp₁ (comp₁ f g) h == comp₁ f (comp₁ g h)
