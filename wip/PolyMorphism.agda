{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Substitution

module wip.PolyMorphism where

  record _→ₚ_ {ℓ} {I J : Type ℓ} (P : Poly I) (Q : Poly J) : Type ℓ where
    field
      Sort→ : I → J
      Op→ : {i : I} → Op P i → Op Q (Sort→ i)
      Param→ : {i : I} {f : Op P i} {j : I} → Param P f j → Param Q (Op→ f) (Sort→ j)
      
      is-cartesian : {i : I} (f : Op P i) →
        is-equiv {A = Arity P f} {B = Arity Q (Op→ f)} (λ { (j , p) → Sort→ j , Param→ p })

  -- Functoriality of various constructions
  module _ {ℓ} {I J : Type ℓ} {P : Poly I} {Q : Poly J} (α : P →ₚ Q) where

    open _→ₚ_ α

    Arity≃ : {i : I} (f : Op P i) → Arity P f ≃ Arity Q (Op→ f)
    Arity≃ f = (λ { (j , p) → Sort→ j , Param→ p }) , is-cartesian f

    ParamSort← : {i : I} {f : Op P i} {j : J}
      → Param Q (Op→ f) j → I
    ParamSort← {f = f} {j = j} p = fst (<– (Arity≃ f) (j , p))

    Param← : {i : I} {f : Op P i} {j : J}
      → (p : Param Q (Op→ f) j) → Param P f (ParamSort← p)
    Param← {f = f} {j} p = snd (<– (Arity≃ f) (j , p))

    Decor→ : {X : J → Type ℓ} {i : I} (f : Op P i)
      → Decor P f (X ∘ Sort→) → Decor Q (Op→ f) X
    Decor→ {X} f ϕ j p = transport X (fst= (<–-inv-r (Arity≃ f) (j , p)))
      ((uncurry ϕ) (<– (Arity≃ f) (j , p)))

    -- Need to say that this gives the original answer when evaluated
    -- on the pushforward of a sort and parameter.

    W→ : {i : I} → W P i → W Q (Sort→ i)
    W→ (lf i) = lf (Sort→ i)
    W→ (nd (f , ϕ)) = nd (Op→ f , Decor→ f (λ j p → W→ (ϕ j p)))

    -- Leaf→ : {i : I} (w : W P i) (j : I)
    --   → Leaf P w j → Leaf Q (W→ w) (Sort→ j)
    -- Leaf→ (lf i) .i idp = idp
    -- Leaf→ (nd (f , ϕ)) j (k , p , l) =
    --   Sort→ k , Param→ p , transport (λ x → Leaf Q x (Sort→ j)) {!!} (Leaf→ (ϕ k p) j l)

