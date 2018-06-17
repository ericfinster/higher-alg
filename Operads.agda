{-# OPTIONS --without-K --rewriting --no-positivity #-}

open import HoTT

module Operads where

  -- Now, I want to setup just a kind of syntax for monads....

  data Mnd : Type₀ → Type₁

  ⟦_⟧ : {I : Type₀} (M : Mnd I) → (I → Type₀) → (I → Type₀)

  η : {I : Type₀} (M : Mnd I) (X : I → Type₀) (i : I) → X i → ⟦ M ⟧ X i 
  bind : {I : Type₀} (M : Mnd I) {X Y : I → Type₀} (i : I) (φ : (i : I) → X i → ⟦ M ⟧ Y i) → ⟦ M ⟧ X i → ⟦ M ⟧ Y i

  μ : {I : Type₀} (M : Mnd I) (X : I → Type₀) (i : I) → ⟦ M ⟧ (⟦ M ⟧ X) i → ⟦ M ⟧ X i 
  μ M X i mm = bind M i (λ i m → m) mm

  mmap : {I : Type₀} (M : Mnd I) {X Y : I → Type₀} (φ : (i : I) → X i → Y i) (i : I) → ⟦ M ⟧ X i → ⟦ M ⟧ Y i
  mmap M φ i m = bind M i (λ i x → η M _ i (φ i x)) m
  
  data Mnd where
    id : (I : Type₀) → Mnd I 
    slc : {I : Type₀} (M : Mnd I) → Mnd (Σ I (⟦ M ⟧ (cst ⊤)))

  -- Interesting.  So yeah, cst ⊤ is not really special.  You can
  -- do a version where you *simultaneously* pull back along a
  -- given fibration Z : I → Type₀.

  -- not strictly positive!
  data Slc {I : Type₀} (M : Mnd I) (X : (Σ I (⟦ M ⟧ (cst ⊤))) → Type₀) : (Σ I (⟦ M ⟧ (cst ⊤))) → Type₀ where
    dot : (i : I) → Slc M X (i , η M (cst ⊤) i tt)
    box : (i : I) (c : ⟦ M ⟧ (cst ⊤) i) (x : X (i , c))
        → (d : ⟦ M ⟧ (λ i₀ → Σ (⟦ M ⟧ (cst ⊤) i₀) (λ c₀ → Slc M X (i₀ , c₀))) i)
        → Slc M X (i , bind M i (λ i₀ → fst) d)

  -- I am shocked that this can be completely defined without
  -- using the fact that the monad is polynomial.  I mean, it's
  -- not strictly positive, but who cares?
  
  -- Okay, I get it.  You can actually *include* the pullback construction
  -- in the definition here.  That's kind of nice, no?
  data GenSlc {I : Type₀} (M : Mnd I) (Z : I → Type₀)
    (X : (Σ I (λ i₀ → (Z i₀) × ⟦ M ⟧ Z i₀)) → Type₀) : (Σ I (λ i₀ → (Z i₀) × ⟦ M ⟧ Z i₀)) → Type₀ where
      gdot : (i : I) (z : Z i) → GenSlc M Z X (i , z , (η M Z i z))
      gbox : (i : I) (z : Z i) (c : ⟦ M ⟧ Z i) (x : X (i , z , c))
             -- → (d : ⟦ M ⟧ (λ i₀ → Σ (Z i₀ × ⟦ M ⟧ Z i₀) (λ c₀ → GenSlc M Z X (i₀ , {!!} , {!!}))) i)
             → GenSlc M Z X (i , {!!})


  ⟦ id I ⟧ X = X
  ⟦ slc M ⟧ X = Slc M X

  -- postulate
  --   hyp : {I : Type₀} (M : Mnd I) (i : I) →
  --         bind M i (λ i₀ → fst) (η M _ i (η M (cst ⊤) i tt , dot i)) == {!!}

  η (id I) X i x = x
  η (slc M) X (i , c) x = {!!}

    where corolla : Slc M X (i , bind M i (λ i₀ → fst) (η M _ i (η M (cst ⊤) i tt , dot i)))
          corolla =  box i c x (η M _ i (η M (cst ⊤) i tt , dot i)) 


  bind = {!!}

  -- Now we can define the M-Opetopes
  Ops : {I : Type₀} (M : Mnd I) → ℕ → Type₀
  Ops {I} M O = I
  Ops M (S n) = Ops (slc M) n

  -- And what's the point?  Well, the hypothesis is that each monad determines
  -- the structure of it's coherent algebras.

  AlgComp : {I : Type₀} (M : Mnd I) (X : I → Type₀) (n : ℕ) (o : Ops M n) → Type₀
  AlgComp M X O i = ⟦ M ⟧ X i → X i       -- the structure
  AlgComp M X (S O) (i , c) = {!!}
  AlgComp M X (S (S n)) o = {!!}          -- the laws

  -- So, the second should say that, for any decoration of c by X
  -- and any decomposition of c (by which one means element of the
  -- slice) the composite function given by eating all the decorations
  -- is equal to the function induced by .... or anyway, something like
  -- this.

  -- Yeah, so now you have to be a bit clever and think of how you
  -- can "manipulate" high dimensional opetopes.  Because what you
  -- want to say is that the "new type" is something like "the sum
  -- of the types of the sources and one for the target".  This would
  -- define "frames" for you.

  Frames : (X : Type₀) (n : ℕ) (o : Ops (id ⊤) n) → Type₀
  Frames X O unit = X
  Frames X (S O) (unit , unit) = Σ X (λ x → Σ X (λ y → x == y))
  Frames X (S (S n)) o = {!!}

  record MSet {I : Type₀} (M : Mnd I) : Type₁ where
    coinductive
    field
      Ob : I → Type₀
