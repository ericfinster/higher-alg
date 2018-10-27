{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Substitution

module Combinators where

  -- My idea is to write a couple of monadic combinators and
  -- attempt to use these when giving complicated proofs of
  -- coherence conditions.

  -- The external hom
  _⇒_ : ∀ {ℓ} {I : Type ℓ} (X Y : I → Type ℓ) → Type ℓ
  _⇒_ {I = I} X Y = (i : I) → X i → Y i

  -- The internal hom (??)
  _⇛_ : ∀ {ℓ} {I : Type ℓ} (X Y : I → Type ℓ) → I → Type ℓ
  _⇛_ {I = I} X Y i = X i → Y i

  module _ {ℓ} {I : Type ℓ} (P : Poly I) where

    -- So here is the polynomial.  Now, let's try to
    -- write the return and bind functions
    Fr : Poly I
    Op Fr = W P
    Param Fr = Leaf P
    
    η-fr : (X : I → Type ℓ) → X ⇒ ⟦ Fr ⟧ X
    η-fr X i x = lf i , λ { .i idp → x }

    μ-fr : (X : I → Type ℓ) → ⟦ Fr ⟧ (⟦ Fr ⟧ X) ⇒ ⟦ Fr ⟧ X
    μ-fr X i (w , ϕ) = graft P w (λ j l → fst (ϕ j l)) ,
      (λ j → graft-leaf-elim P w (λ j l → fst (ϕ j l)) j (cst (X j))
                             (λ k l m → snd (ϕ k l) j m))

    -- Yeah, you might play with the ordering of the signature here ...
    bind-fr : {X Y : I → Type ℓ} → (i : I) → ⟦ Fr ⟧ X i → X ⇒ ⟦ Fr ⟧ Y → ⟦ Fr ⟧ Y i
    bind-fr {Y = Y} i (w , ϕ) f = graft P w (λ j l → fst (f j (ϕ j l))) ,
      (λ j → graft-leaf-elim P w (λ j l → fst (f j (ϕ j l))) j (cst (Y j))
                             (λ k l m → snd (f k (ϕ k l)) j m))

  module _ {ℓ} {I : Type ℓ} (P : Poly I) where

    Subst : Poly (Ops P)
    Subst = P // FrameRel P

    -- So, I'll call this the substitution monad.
    -- Let's try and define its operations

    η-subst : (X : Ops P → Type ℓ) → X ⇒ ⟦ Subst ⟧ X
    η-subst X (i , f) x = (corolla P f , corolla-lf-eqv P f , lift tt) ,
      λ { .(_ , _) (inl idp) → x ;
          f (inr (j , g , ())) }

    μ-subst : (X : Ops P → Type ℓ) → ⟦ Subst ⟧ (⟦ Subst ⟧ X) ⇒ ⟦ Subst ⟧ X
    μ-subst X (i , f) ((w , α , u) , κ) =
      (substitute (FrameRel P) w (λ g n → {!fst (κ g n)!}) , {!!} , u) , {!!}
