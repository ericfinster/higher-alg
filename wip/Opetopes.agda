{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Substitution
open import SubstCoh
open import Monad
open import Globularity

-- Opetopes and their realizations
module Opetopes {ℓ} {I : Type ℓ} (P : Poly I) (X : OpetopicType P (FrameRel P)) where

  Opetope : ℕ → Type ℓ
  
  OpPoly : (n : ℕ) → Poly (Opetope n)
  OpRel : (n : ℕ) → PolyRel (OpPoly n)
  OpType : (n : ℕ) → OpetopicType (OpPoly n) (OpRel n)

  Opetope O = I
  Opetope (S n) = Ops (OpPoly n)

  OpPoly O = P
  OpPoly (S n) = OpPoly n // ΣR (OpRel n) (Ref (OpType n))

  OpRel O = FrameRel P
  OpRel (S n) = FlattenRel (ΣR (OpRel n) (Ref (OpType n)))

  OpType O = X
  OpType (S n) = Hom (OpType n)

  -- Hmmm. Completely crazy.  Because it looks like if we assume that
  -- the refinement is trivial, then we can complete this.  But then
  -- that starts to look very much like the multiplicative structure
  -- on the universe, no?
  umm : (n : ℕ) {o : Opetope n} (p : Op (OpPoly n) o)
    → (w : W (OpPoly (S n)) (o , p))
    → OpRel n (flatten (ΣR (OpRel n) (Ref (OpType n))) w) p
              (flatten-frm (ΣR (OpRel n) (Ref (OpType n))) w)
  umm O p w = lift tt
  umm (S n) {τ , σ} (w , α , (r , s)) coh = (umm n σ (flatten R₁ coh) , t) ,
    globularity (OpRel n) (Ref (OpType n)) (Ref (Hom (OpType n))) w α (r , s)
      coh (umm n σ (flatten R₁ coh) , t) {!!}

    where R₀ = (ΣR (OpRel n) (Ref (OpType n)))
          R₁ = (ΣR (FlattenRel R₀) (Ref (Hom (OpType n))))

          t : Ref (OpType n) (flatten R₀ (flatten R₁ coh)) σ
                (flatten-frm R₀ (flatten R₁ coh)) (umm n σ (flatten R₁ coh))
          t = {!!}

  -- Yeah, so, like.  It's similar to below where I need ummm n to be
  -- equal to any other guy.  But can't you prove this by induction?

  -- I think you have to try.  Because that base case looks pretty fucking
  -- trivial.  And if this were in fact true, I feel like it's really
  -- close to the coherent structure on the universe.

  -- Ummm.  But wait, do I even need it to be contractible?
  -- because, like, I already have the globular equalities,
  -- so the element can be just obtained by transport from r, no?

  -- Hold on, hold on.  Doesn't this show ... it's like.  You've
  -- constructed this magma.  And then you need to show, to have
  -- the universe, that every composite is give by this one.
  -- On the other hand, I feel like the witnesses in the next
  -- level are exactly the statement that it *is* this one.

  -- So there's something funny going on here.  In any case, I
  -- didn't expect something so interesting to pop out of this.
  -- But it seems something kinda cool is happening.

  ∂Op : (n : ℕ) {o : Opetope n} (p : Op (OpPoly n) o) → Type ℓ
  ●Op : (n : ℕ) {o : Opetope n} (p : Op (OpPoly n) o) → Type ℓ
  in-∂Op : (n : ℕ) {o : Opetope n} (p : Op (OpPoly n) o) → ∂Op n p → ●Op n p

  ∂W : (n : ℕ) {o : Opetope n} (w : W (OpPoly n) o) → Type ℓ
  ●W : (n : ℕ) {o : Opetope n} (w : W (OpPoly n) o) → Type ℓ
  in-∂W : (n : ℕ) {o : Opetope n} (w : W (OpPoly n) o) → ∂W n w → ●W n w

  -- Exactly!
  ∂-equiv : (n : ℕ) {o : Opetope n} (p : Op (OpPoly n) o)
    → (w : W (OpPoly n) o) (α : Frame (OpPoly n) w p) (r : OpRel n w p α)
    -- → (r : ΣR (OpRel n) (Ref (OpType n)) w p α)
    → ∂Op n p ≃ ∂W n w

  ∂Op O f = ⊤ ⊔ Arity P f
  ∂Op (S n) {o , p} (w , α , r) =
    Pushout (span (●Op n p) (●W n w) (∂Op n p)
                  (in-∂Op n p)
                  ((in-∂W n w) ∘ –> (∂-equiv n p w α (fst r))))

  ●Op n p = ⊤ * (∂Op n p) 
  in-∂Op n p = jright

  -- Now, what is the ∂ of a successor tree?
  ∂W O w = ⊤ ⊔ Σ I (Leaf P w)
  ∂W (S n) {o , p} w = 
    Pushout (span (●Op n p) (●W n canopy) (∂Op n p)
                  (in-∂Op n p)
                  (in-∂W n (canopy) ∘ –> (∂-equiv n p canopy canopy-frm (umm n p w)))) 

    where canopy : W (OpPoly n) o
          canopy = flatten (ΣR (OpRel n) (Ref (OpType n))) w

          canopy-frm : Frame (OpPoly n) canopy p
          canopy-frm = flatten-frm (ΣR (OpRel n) (Ref (OpType n))) w

  -- Bingo.  So the point then is that we need to extract this
  -- descending relation in order to know that this is well defined.

  -- The conjecture (which would be completely crazy!) is that we can
  -- in fact do this for any opetopic type, and that this follows and
  -- is the essential statement of globularity.

  ●W O (lf i) = Lift ⊤
  ●W O (nd (f , ϕ)) = ⊤ * (Σ (Arity P f) (λ a → ●W O (ϕ (fst a) (snd a))))
  ●W (S n) w = {!!}

  -- Excellent!!
  in-∂W O (lf i) (inl tt) = lift tt
  in-∂W O (lf i) (inr (.i , idp)) = lift tt
  in-∂W O (nd (f , ϕ)) (inl tt) = jleft tt
  in-∂W O (nd (f , ϕ)) (inr (j , k , p , l)) =
    jright ((k , p) , (in-∂W O (ϕ k p) (inr (j , l))))
  in-∂W (S n) w = {!!}

  -- And here's where I think we will have to work...
  ∂-equiv O p w α r = ⊔-emap (ide ⊤) (Σ-emap-r (λ j → (α j)⁻¹))
  ∂-equiv (S n) ._ w ._ ((r , s) , idp) =
    Pushout-emap ((span-map (idf _) (idf _) (idf _)
      (comm-sqr (λ x → idp))
      (comm-sqr (λ x → {!!}))) ,
      (idf-is-equiv _ , idf-is-equiv _ , idf-is-equiv _))

  -- So then it looks like we just have to show that the
  -- equivalence obtained here doesn't depend on the element
  -- chosen.  But is that true?

  -- The realization of an opetope is always just the filled
  -- version of itself viewed as an operation as above...
  𝕆 : {n : ℕ} → Opetope n → Type ℓ
  𝕆 {O} i = Lift ⊤
  𝕆 {S n} (o , p) = ●Op n p
