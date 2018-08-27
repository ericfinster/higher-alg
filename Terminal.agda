{-# OPTIONS --without-K --rewriting --type-in-type #-}

open import HoTT
open import Util
open import Polynomial
open import Substitution
open import PolyMonad
open import Morphism

-- Attempting to construct the terminal cart-poly-monad.
module Terminal where

  𝕌 : Poly ⊤
  γ 𝕌 unit = Type₀
  ρ 𝕌 X unit = X

  TermFamily : {I : Type₀} (P : Poly I) → FillingFamily P
  TermFamily P w c f = ⊤

  is-contr-fam : {I : Type₀} {P : Poly I} (F : FillingFamily P) → Type₀
  is-contr-fam {I} {P} F = {i : I} (w : W P i) (c : γ P i) (f : Frame P w c) → is-contr (F w c f)

  TermDomain : {I : Type₀} (P : Poly I) → PolyDomain P
  F (TermDomain P) = TermFamily P
  H (TermDomain P) = TermDomain (P // TermFamily P)

  -- Here's another possibility: say that a polynomial is "univalent"
  -- if, for every tree in the polynomial, the type of pairs of a constructor
  -- and a frame is contractible.  (That is, without the filling family).

  -- Is it possible that this property is inherited by the filling poly
  -- of the terminal family?

  is-univalent : {I : Type₀} (P : Poly I) → Type₀
  is-univalent {I} P = {i : I} (w : W P i) → is-contr (Σ (γ P i) (Frame P w))
  
  module _ {I : Type₀} (P : Poly I) (is-u : is-univalent P) where

    TF = TermFamily P
    
    -- So, this is somewhat interesting.  It almost looks like it might be true.
    -- Whoa.  So the assertion is that, in the univalent situation, the baez-dolan
    -- substitution is strongly unique in the given sense.
    conjecture : is-univalent (P // TermFamily P)
    conjecture {i , c} pd = has-level-in (ctr , pth) 

      where ctr : Σ (Σ (W P i) (λ w → Σ (Frame P w c) (TermFamily P w c))) (Frame (P // (TermFamily P)) pd)
            ctr = (flatten TF pd  , flatten-frm TF pd , tt) , bd-frame TF pd

            pth : (a : Σ (Σ (W P i) (λ w → Σ (Frame P w c) (TermFamily P w c))) (Frame (P // (TermFamily P)) pd)) → ctr == a
            pth ((w , f₀ , tt) , f₁) = {!!}


    -- Could this in fact be correct? 

    -- What happens in the base case?  Our pasting diagram is a leaf.  We have to
    -- find a tree a frame and so on.  Now, because of the last term, we can only
    -- have a single node.  So it "has to be" a corolla.  But then, the corolla has
    -- a frame to c, always.  And so, if the tree must be a corlla, the only possible
    -- equivalence will be the given one.  (over and endo of c).

    -- conjecture {i , c} (lf .(i , c)) = has-level-in (((corolla P c , corolla-lf-eqv P c , tt) , {!!}) , {!!})
    -- conjecture (nd {i , c} ((w , f , tt) , δ)) = {!!}

  module _ {I : Type₀} {P : Poly I} (F : FillingFamily P) where

    -- Okay, my idea is instead of having a function which computes
    -- composites of constructors, what if I had a function which
    -- computed composites of *fillers*

    postulate

      fill-comp : {i : I} {c : γ P i}
        → (pd : W (P // F) (i , c))
        → F (flatten F pd) c (flatten-frm F pd)
        
    -- FF : FillingFamily (P // F)
    -- FF {i , c} pd (w , f , x) ff = (w , f , x , ff) == (flatten F pd , flatten-frm F pd , fill-comp pd , bd-frame F pd)


  module _ {I : Type₀} {P : Poly I} (F₀ : FillingFamily P) where

    record BDWitness {i : I} {c : γ P i} (pd : W (P // F₀) (i , c))
      (w : W P i) (f₀ : Frame P w c) (x₀ : F₀ w c f₀)
      (f₁ : Frame (P // F₀) pd (w , f₀ , x₀)) : Type₀ where
      constructor bd-wit
      field
        p₀ : w == flatten F₀ pd
        p₁ : f₀ == flatten-frm F₀ pd [ (λ a → Frame P a c) ↓ p₀ ]
        p₂ : f₁ == bd-frame F₀ pd [ (λ a → Frame (P // F₀) pd a) ↓ pair= p₀ (↓-Σ-in p₁ (to-transp-↓ (uncurry (λ a → F₀ a c)) (pair= p₀ p₁) x₀)) ] 

    BDFam : FillingFamily (P // F₀)
    BDFam pd (w , f₀ , x₀) f₁ = BDWitness pd w f₀ x₀ f₁

    bd-fam-eqv : {i : I} (c : γ P i) (pd : W (P // F₀) (i , c))
      → CompositeFor BDFam pd
      ≃ F₀ (flatten F₀ pd) c (flatten-frm F₀ pd)
    bd-fam-eqv c pd = equiv to from to-from from-to

      where to : CompositeFor BDFam pd → F₀ (flatten F₀ pd) c (flatten-frm F₀ pd)
            to ((._ , ._ , x) , ._ , (bd-wit idp idp idp)) = x

            from : F₀ (flatten F₀ pd) c (flatten-frm F₀ pd) → CompositeFor BDFam pd
            from x = (flatten F₀ pd , flatten-frm F₀ pd , x) , bd-frame F₀ pd , (bd-wit idp idp idp)

            to-from : (x : F₀ (flatten F₀ pd) c (flatten-frm F₀ pd)) → to (from x) == x
            to-from x = idp

            from-to : (cmp : CompositeFor BDFam pd) → from (to cmp) == cmp
            from-to ((._ , ._ , x) , ._ , (bd-wit idp idp idp)) = idp

  -- Wait, we don't need to do this as an extension.  It's perfectly
  -- well defined as is ....
  BDDom : {I : Type₀} (P : Poly I) (F : FillingFamily P) → PolyDomain (P // F)
  F (BDDom P F) = BDFam F
  H (BDDom P F) = BDDom (P // F) (BDFam F)

  -- Well, holy shit.  That is much, much easier.
  -- No stupid extension, no pulling back.
  -- You just directly fill the higher dimensions with the witnesses giving the right answer.

  -- Okay, so from this, it follows quite clearly that if F₀ is contractible, then the
  -- next guy has unique composites.

  -- But we fall into the same dilemma: it does not at all look like the witness type is
  -- contractible merely on the assumption that F₀ is.  And since we can already show
  -- that the type of composites is the witness type in the next dimension, then we have
  -- unique composites if and only if it *is* unique.

  -- So this is a bit of a puzzle.

  -- It seems that either this is the wrong approach, or else some kind of miracle happens
  -- and the *double* witness type is always contractible ...

  -- Uh, yeah, so is it possible, this outrages double witness conjecture?  I mean, you
  -- had always thought that somehow the basic idea should be that baez-dolan substitution
  -- was infinitely coherent.  Perhaps this is the way you finally express that .....
  -- I mean, it does, after all, seem to be merely a statement about the behavior of
  -- substitution, and nothing else.  Let's try to think about it ...

  --
  --  Older stuff ....
  --
  
  --   -- The canonical extension, adding a witness that fillers are always
  --   -- in baez-dolan frames.
  --   BDExt : (F₁ : FillingFamily (P // F₀)) → Extension F₁
  --   BDExt F₁ {i , c} pd (w , f₀ , x₀) f₁ x₁ = BDWitness pd w f₀ x₀ f₁
  
  --   coh-eqv : (F₁ : FillingFamily (P // F₀))
  --     → {i : I} (c : γ P i) (pd : W (P // F₀) (i , c))
  --     → CompositeFor (ΣFam F₁ (BDExt F₁)) pd 
  --     ≃ CoherenceFor F₁ pd
  --   coh-eqv F₁ c pd = equiv to from to-from from-to

  --     where to : CompositeFor (ΣFam F₁ (BDExt F₁)) pd → CoherenceFor F₁ pd
  --           to ((._ , ._ , x₀) , ._ , x₁ , bd-wit idp idp idp) = x₀ , x₁

  --           from : CoherenceFor F₁ pd → CompositeFor (ΣFam F₁ (BDExt F₁)) pd
  --           from (x₀ , x₁) = (flatten F₀ pd , flatten-frm F₀ pd , x₀) , bd-frame F₀ pd , x₁ , bd-wit idp idp idp

  --           to-from : (coh : CoherenceFor F₁ pd) → to (from coh) == coh
  --           to-from (x₀ , x₁) = idp

  --           from-to : (cmp : CompositeFor (ΣFam F₁ (BDExt F₁)) pd) → from (to cmp) == cmp
  --           from-to ((._ , ._ , x₀) , ._ , x₁ , bd-wit idp idp idp) = idp

  -- {-# TERMINATING #-}
  -- BDDomain : {I : Type₀} (P : Poly I) (F₀ : FillingFamily P)
  --   → PolyDomain (P // F₀)
  --   → PolyDomain (P // F₀)
  -- F (BDDomain P F₀ D) = ΣFam (F D) (BDExt F₀ (F D))
  -- H (BDDomain P F₀ D) = Domain← (ExtendedFst (F D) (BDExt F₀ (F D))) (BDDomain (P // F₀) (F D) (H D))

