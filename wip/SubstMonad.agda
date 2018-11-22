{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Substitution
open import PolyMonad
open import Generating

module SubstMonad where

  open BinaryOp
  open BinaryLaws

  module _ {ℓ} {I : Type ℓ} (P : Poly I) where

    TrivRel : PolyRel P
    TrivRel _ _ = Lift ⊤
  
    SubstInv : SubInvar TrivRel
    SubstInv _ = lift tt

    SubstPoly : Poly (Ops P)
    SubstPoly = P // TrivRel
    
    subst-η : (f : Ops P) → Op SubstPoly f
    subst-η (i , f) = (corolla P f , corolla-frm P f) , lift tt

    subst-η-frm : (f : Ops P) (g : Ops P) → (f == g) ≃ Param SubstPoly (subst-η f) g
    subst-η-frm f = bd-frm TrivRel (lf f)

    subst-γ : {f : Ops P} (w : Op SubstPoly f) (κ : Decor SubstPoly w (Op SubstPoly)) → Op SubstPoly f
    subst-γ ((w , α) , r) κ = 
      (subst P w (λ g n → fst (κ g n)) , λ j → (α j) ∘e (subst-lf-eqv P w (λ g n → fst (κ g n)) j)) , r

    postulate
    
      subst-γ-frm : {f : Ops P} (w : Op SubstPoly f) (κ : Decor SubstPoly w (Op SubstPoly)) (g : Ops P)
        → Σ (Ops P) (λ h → Σ (Param SubstPoly w h) (λ n → Param SubstPoly (κ h n) g))
          ≃ Param SubstPoly (subst-γ w κ) g

    SubstBin : BinaryOp SubstPoly
    η SubstBin = subst-η
    η-frm SubstBin = subst-η-frm 
    γ SubstBin = subst-γ
    γ-frm SubstBin = subst-γ-frm


    postulate

      SubstLaws : BinaryLaws SubstPoly SubstBin

  -- Okay, what is my idea?
  SubstCoh : ∀ {ℓ} {I : Type ℓ} (P : Poly I)
    → CohStruct (BinMgm (SubstPoly P) (SubstBin P))
  Ψ (SubstCoh P) = μ-invar (SubstPoly P) (SubstBin P) (SubstLaws P)
  H (SubstCoh P) = {!!}

    where coind : CohStruct (BinMgm (SubstPoly (SubstPoly P)) (SubstBin (SubstPoly P)))
          coind = SubstCoh (SubstPoly P)

  -- Bingo.  That's it.
  
  -- The point is that by the coinduction hypothesis, you have an
  -- infinite coherence tower for the *substitution* monad one
  -- dimension higher.

  -- Your goal, then, is to show that this coherence tower can be
  -- "lifted" to be compatible with the slice relation in the lowest
  -- dimension.

  -- Wow.  This looks really, really good.  It's going to be a lot
  -- of work, but I think this is really the idea.
