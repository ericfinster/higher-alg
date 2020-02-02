{-# OPTIONS --without-K --rewriting --type-in-type #-}

open import HoTT
open import wip.Indexed

module wip.OpetopicType where

  IdPoly : Poly ⊤ ⊤
  IdPoly A τ tt = is-contr A

  postulate
    X₀ : ⊤ → Set

  XPoly : Poly (Σ ⊤ X₀) (Σ ⊤ X₀)
  XPoly = PbPoly IdPoly X₀

  Tr₁ : (x : Σ ⊤ X₀) (L : Set) (Lτ : L → Σ ⊤ X₀) (N : Set) (Nτ : N → Op XPoly) → Set
  Tr₁ = Tr XPoly

    -- data Tr : I → (L : Set) → (L → I) → (N : Set) → (N → Op P) → Set where
    --   lf : {i : I} → Tr i ⊤ (λ _ → i) ⊥ λ { () }
    --   nd : (A : Set) (τ : A → I) (i : I) (f : P A τ i) 
    --        → (l : A → Set) (lt : (a : A) → l a → I)
    --        → (n : A → Set) (nt : (a : A) → n a → Op P)
    --        → (δ : (a : A) → Tr (τ a) (l a) (lt a) (n a) (nt a))
    --        → Tr i (Σ A l) (λ { (a , l₀) → lt a l₀ }) (⊤ ⊔ Σ A n)
    --               (λ { (inl tt) → A , τ , i , f ;
    --                    (inr (a , n₀)) → nt a n₀ })

  -- Ar : Set
  -- Ar = Σ X₀ (λ x → Σ X₀ (λ y → X₁ x y))

  -- data Tr₁ : X₀ → (L : Set) (Lτ : L → X₀) (N : Set) (Nτ : N → Ar) → Set where
  --   lf₁ : (x : X₀) → Tr₁ x ⊤ (cst x) ⊥ (λ { () })
  --   nd₁ : (x : X₀) (y : X₀) (f : X₁ x y) (L : Set) (Lτ : L → X₀) (N : Set) (Nτ : N → Ar)
  --         → Tr₁ y L Lτ N Nτ  -- I mean, here, you mean sum L with a contractible type ...
  --         → Tr₁ x L Lτ (⊤ ⊔ N) (λ { (inl tt) → (x , y , f) ;
  --                                   (inr n) → Nτ n })

  -- -- Umm, right, but now this is missing some data.
  -- postulate
  --   X₂ : (x : X₀) (L : Set) (Lτ : L → X₀) (N : Set) (Nτ : N → Ar)
  --        (pd : Tr₁ x L Lτ N Nτ) → Set

  -- -- 2Cell : Set
  -- -- 2Cell = {!!}

  -- -- data Tr₂ : (x : X₀) (y : X₀) (N₀ : Set) (τ₀ : N₀ → Ar) (t : Tr₁ x y N₀ τ₀)
  -- --            (N₁ : Set) (τ₁ : N₁ → 2Cell) → Set where
  -- --   lf₂ : {!!} → Tr₂ {!!} {!!} {!!} {!!} {!!} {!!} {!!}
            
       

