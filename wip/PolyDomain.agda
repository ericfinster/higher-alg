{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Substitution
open import SubstCoh
open import Globularity

module PolyDomain where

  -- Okay, here's the naive polynomial domain
  record PolyDomain {ℓ} {I : Type ℓ} (P : Poly I) : Type (lsucc ℓ) where
    coinductive
    field
    
      R : PolyRel P
      D : PolyDomain (P // R)

  open PolyDomain
  
  module _ {ℓ} {I : Type ℓ} (P : Poly I) (X : PolyDomain P) where

    PSort : (n : ℕ) → Type ℓ
    PPoly : (n : ℕ) → Poly (PSort n)
    PDom : (n : ℕ) → PolyDomain (PPoly n)

    PSort O = I
    PSort (S n) = Ops (PPoly n)

    PPoly O = P
    PPoly (S n) = PPoly n // R (PDom n)

    PDom O = X
    PDom (S n) = D (PDom n)

    coh₀ : {i : I} {f : Op P i} (pd : W (P // R X) (i , f)) → Type ℓ
    coh₀ {i} {f} pd = Σ (R X (flatten (R X) pd) f (flatten-frm (R X) pd))
      (λ r₀ → R (D X) pd (flatten (R X) pd , flatten-frm (R X) pd , r₀) (bd-frame (R X) pd))

    -- Okay, so the previous can be generalized for a polynomial
    -- and there should be some kind of map that we are going to
    -- assert is an equivalence.  Let's try this.

    Coh₀ : {n : ℕ} (f : PSort (S n)) (w : W (PPoly (S n)) f) → Type ℓ
    Coh₀ {n} (i , f) w = Σ (R (PDom n) (flatten (R (PDom n)) w) f (flatten-frm (R (PDom n)) w))
      (λ r₀ → R (D (PDom n)) w (flatten (R (PDom n)) w , flatten-frm (R (PDom n)) w , r₀) (bd-frame (R (PDom n)) w))

    Cmp₀ : {n : ℕ} (f : PSort (S n)) (w : W (PPoly (S n)) f) → Type ℓ
    Cmp₀ {n} (i , f) w = Σ (Op (PPoly n // R (PDom n)) (i , f)) (λ m →
      Σ (Frame (PPoly n // R (PDom n)) w m) (λ β → R (PDom (S n)) w m β))

    coh-to-comp₀ : {n : ℕ} (f : PSort (S n)) (w : W (PPoly (S n)) f)
      → Coh₀ f w → Cmp₀ f w
    coh-to-comp₀ {n} (i , f) w (r₀ , r₁) =
      (flatten (R (PDom n)) w , flatten-frm (R (PDom n)) w , r₀) ,
        bd-frame (R (PDom n)) w , r₁

    -- And now, what happens?  Well, when I consider a pasting diagram
    -- in the double successor, I can do two things.  First, I can use
    -- this property to extract two chosen elements.  Then, projecting
    -- on the first, I will find a composite of the flattened guy.  I can
    -- then extract two elements from this.

    Coh₁ : {n : ℕ} {i : PSort n} {f : Op (PPoly n) i}
      → (w : Op (PPoly (S n)) (i , f))
      → (coh : W (PPoly (S (S n))) ((i , f) , w))
      → Type ℓ
    Coh₁ {n} {i} {f} (w , α , r) coh = Σ (Coh₀ (i , f) (flatten (R (PDom (S n))) coh))
      (λ { (r₀ , r₁) → R (D (D (PDom n))) coh (flatten (R (PDom (S n))) coh , flatten-frm (R (PDom (S n))) coh , {!!})
        (bd-frame (R (PDom (S n))) coh) })

    -- Great, and now this time, what is a coherence?  Well, I mean,
    -- why don't you just ask for an identification of w with the
    -- double flatten, and so on.  That is, ask for a coherence of this
    -- guy, an identification of w with the double flatten and so on.

    -- Hmmm.  No, this seems suspicious.  Don't you need, at some point,
    -- to *use* the calculation which should identify the double flatten
    -- with w?


    -- On the other hand, I can simply forget the top element, and extract
    -- immediately.  And I guess this point is that the resulting elements
    -- should be equal over some canonical identification of the previous
    -- dimensions pasting diagram with the flattening of the original.

    -- Hmm.  But it seems that globularity might be slightly more difficult
    -- to prove in the current setup.

    Coh-to-op₀ : {n : ℕ} (f : PSort (S n)) (w : W (PPoly (S n)) f)
      → Coh₀ f w → PSort (S (S (S n)))
    Coh-to-op₀ {n} (i , f) w (r₀ , r₁) =
      ((i , f) , flatten (R (PDom n)) w , flatten-frm (R (PDom n)) w , r₀) ,
        w , bd-frame (R (PDom n)) w , r₁

    -- Well, yes, but perhaps the idea is not to asset that this commutes,
    -- but rather to distinguish the space of well formed "two composites".

    -- Is this possible?


