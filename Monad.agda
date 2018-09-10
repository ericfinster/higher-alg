{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Substitution

module Monad where

  record OpDom {ℓ} {I : Type ℓ} (P : Poly I) (C : CartesianRel P) : Type (lsucc ℓ) where
    coinductive
    field

      Fillers : {i : I} (w : W P i) (f : Op P i) (r : fst C w f) → Type ℓ
      HomDom : OpDom (P // fst C) (FlattenRel C) -- Oh, don't you mean the extended relation here?

  open OpDom
  
  record is-algebraic {ℓ} {I : Type ℓ} {P : Poly I}
    {C : CartesianRel P} (R : OpDom P C) : Type ℓ where
    coinductive
    field

      has-fillers : {i : I} (w : W P i) → is-contr (Σ (Op P i) (λ f → Σ (fst C w f) (λ r → Fillers R w f r)))
      hom-has-fillers : is-algebraic (HomDom R)

  open is-algebraic

  FrameRel : ∀ {ℓ} {I : Type ℓ} (P : Poly I) → CartesianRel P
  FrameRel P = Frame P , λ w f → idf _
  
  TerminalDom : ∀ {ℓ} {I : Type ℓ} (P : Poly I) (C : CartesianRel P) → OpDom P C
  Fillers (TerminalDom P C) w f r = Lift ⊤
  HomDom (TerminalDom P C) = TerminalDom (P // fst C) (FlattenRel C)

  -- So, what did you want to prove?
  -- Well, the claim should be that if you are known to be algebraic with
  -- respect to some cartesian relation, then you are algebraic for the
  -- terminal domain.
  
  conj : ∀ {ℓ} {I : Type ℓ} (P : Poly I) (C : CartesianRel P)
    → (is-alg : {i : I} (w : W P i) → is-contr (Σ (Op P i) (λ f → fst C w f)))
    → (σ : {g : Ops P} (pd : W (P // (fst C)) g) → fst C (flatten C pd) (snd g))
    → is-algebraic (TerminalDom P C)
  has-fillers (conj P C is-alg σ) w = {!!} -- this is now trivial ..
  hom-has-fillers (conj P C is-alg σ) = conj (P // fst C) (FlattenRel C) thm {!!}

    where thm : {g : Ops P} (pd : W (P // (fst C)) g) 
                → is-contr (Σ (Σ (W P (fst g)) (λ w → fst C w (snd g))) (fst (FlattenRel C) pd))
          thm (lf (i , g)) = has-level-in (((corolla P g , {!!}) , idp) , {!!})
          thm {i , g} (nd ((w , r) , ϕ)) = {!!}

    -- where thm : {g : Ops P} (pd : W (P // (fst C)) g) 
    --             → is-contr (Σ (Σ (W P (fst g)) (λ w → fst C w (snd g))) (fst (FlattenRel C) pd))
    --       thm {g} pd = has-level-in (ctr , pth)

    --         where ctr : Σ (Σ (W P (fst g)) (λ w → fst C w (snd g))) (fst (FlattenRel C) pd)
    --               ctr = (flatten C pd , σ pd) , idp

    --               pth : (y : Σ (Σ (W P (fst g)) (λ w → fst C w (snd g))) (fst (FlattenRel C) pd)) → ctr == y
    --               pth ((._ , r) , idp) = pair= {!contr-has-all-paths ⦃ is-alg (flatten C pd) ⦄ (snd g , σ pd) (snd g , r)!} {!!}


  -- Okay, not completely trivial.
  -- You sill have to think about this a bit....
  -- Hmmm.  So no, something here doesn't look quite right.

  -- Yeah, you're going to have to give this some time and think a bit.
  -- What was the idea?

  -- Oh yes, the thing was, you wanted to think about your "coherence condition"
  -- from the previous version as being correct.  That is, coherences are somes
  -- of two consecutive extension witnesses.  And dominoes.

  -- And indeed, the second looks like it should be an instance of
  -- globularity, which I think indeed should hold for FlattenRel C.

  -- Right.  Still not completely clear.

  -- But anyway, you should calculate a couple of coherences to get used to the
  -- new picture.  Maybe when you have a bit more experience with the setup,
  -- the right idea will follow.

  -- Hmmm.  But were you supposed to slice it once?
