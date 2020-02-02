{-# OPTIONS --without-K --rewriting --type-in-type #-}

open import HoTT

module wip.Indexed where

  Poly : Set → Set → Set
  Poly I J = (A : Set) → (A → I) → J → Set

  Op : ∀ {I} → Poly I I → Set
  Op {I} P = Σ (Set) (λ A → Σ (A → I) (λ τ → Σ I (λ j → P A τ j)))

  PbPoly : ∀ {I} → Poly I I → (X : I → Set) → Poly (Σ I X) (Σ I X)
  PbPoly {I} P X A τ (i , x) = P A (fst ∘ τ) i × ((a : A) → X (fst (τ a)))

  ⟦_⟧ : ∀ {I J} → Poly I J → (I → Set) → (J → Set)
  ⟦_⟧ {I} {J} P X j = Σ Set (λ A → Σ (A → I) (λ τ → P A τ j × ((a : A) → X (τ a))))

  record PMgm {I : Set} (P : Poly I I) : Set where
    field
      μ-lf : {i : I} → P ⊤ (λ _ → i) i
      μ-nd : {A : Set} {τ : A → I} {i : I} (f : P A τ i)
             → (l : A → Set) (lτ : (a : A) → l a → I)
             → (δ : (a : A) → P (l a) (lτ a) (τ a))
             → P (Σ A l) (uncurry lτ) i

  module _ {I} (P : Poly I I) where
    
    data Tr : I → (L : Set) → (L → I) → (N : Set) → (N → Op P) → Set where
      lf : {i : I} → Tr i ⊤ (λ _ → i) ⊥ λ { () }
      nd : (A : Set) (τ : A → I) (i : I) (f : P A τ i) 
           → (l : A → Set) (lt : (a : A) → l a → I)
           → (n : A → Set) (nt : (a : A) → n a → Op P)
           → (δ : (a : A) → Tr (τ a) (l a) (lt a) (n a) (nt a))
           → Tr i (Σ A l) (λ { (a , l₀) → lt a l₀ }) (⊤ ⊔ Σ A n)
                  (λ { (inl tt) → A , τ , i , f ;
                       (inr (a , n₀)) → nt a n₀ })

    -- Interesting.  There it is.  This is a sort of maximally indexed
    -- presentation of the tree where we have exposed both its leaf and
    -- node types.  Now, can you write the type of the substitution
    -- operation?  And then keep going?

    Mgm : Set
    Mgm = ∀ i L Lτ N Nτ → Tr i L Lτ N Nτ → P L Lτ i

    Subst : Poly (Op P) (Op P)
    Subst N nτ (L , Lτ , i , f) = Tr i L Lτ N nτ

  -- So, okay, I claim that for any polynomial, there is a magma structure
  -- on its slice.  Now, what would change if P already had a magma structure?
  -- Well, the point is that then, the constructors of the slice would change,
  -- since you would ask that the constructor in the input above be related
  -- to the tree by the magma relation.

  -- Ummm.  Yeah.  So what to do with this idea?  Because it seems like what
  -- is still going to happen is that you have to describe this infinite tower
  -- of multiplications in the slice.  So maybe the point is just to see if
  -- you can actually write out a couple iterations of the tree structure in
  -- the universe.  Because I feel like what is going to happen is that the types
  -- of the constructors are going to get more precise as you go, and that this
  -- is kind of the whole point.

  

