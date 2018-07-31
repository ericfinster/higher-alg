{-# OPTIONS --without-K --rewriting --type-in-type #-}

open import HoTT
open import Util
open import Polynomial
open import PolyDomain
open import Substitution
open import SubstCoh
open import PolyMonad

module Examples where

  𝕌 : Poly ⊤
  γ 𝕌 unit = Type₀
  ρ 𝕌 X unit = X

  TermFamily : {I : Type₀} (P : Poly I) → FillingFamily P
  TermFamily P w c f = ⊤

  TermDomain : {I : Type₀} (P : Poly I) → PolyDomain P
  F (TermDomain P) = TermFamily P
  H (TermDomain P) = TermDomain (P // TermFamily P)


  -- Okay, what's the idea?  First, if I have a polynomial
  -- and a morphism, I should be able to pull back filling families.

  PbFam : {I : Type₀} {P : Poly I} (F : FillingFamily P)
    → (Q : PolyOver P) → FillingFamily (ΣPoly Q)
  PbFam F Q w (c , d) f = F (W-map Q w) c (λ k → {!!})
  
  -- So, a little calculation to do there.  But what
  -- are the consequences?  I would like to say that
  -- this is on the way to pulling back domains.

  InducedOver : {I : Type₀} {P : Poly I} (F : FillingFamily P)
    → (Q : PolyOver P)
    → PolyOver (P // F)
  Idx (InducedOver F Q) (i , c) = Σ (Idx Q i) (λ j → Cns Q j c)
  Cns (InducedOver F Q) {i , c} (j , d) (w , f , x) = {!!}
  Plc (InducedOver F Q) = {!!}
  plc-contr (InducedOver F Q) = {!!}

  -- Hmm.  Okay.  And what's the idea?  Well, obviously we want
  -- a "tree over w" and a frame over, etc...

  IdxEquiv : {I : Type₀} {P : Poly I} (F : FillingFamily P)
    → (Q : PolyOver P)
    → Σ (Σ I (Idx Q)) (γ (ΣPoly Q))
    ≃ Σ (Σ I (γ P)) (Idx (InducedOver F Q))
  IdxEquiv {I} {P} F Q = equiv to from to-from from-to

    where to : Σ (Σ I (Idx Q)) (γ (ΣPoly Q)) → Σ (Σ I (γ P)) (Idx (InducedOver F Q))
          to ((i , q) , (c , d)) = (i , c) , (q , d)

          from : Σ (Σ I (γ P)) (Idx (InducedOver F Q)) → Σ (Σ I (Idx Q)) (γ (ΣPoly Q)) 
          from ((i , c) , (q , d)) = (i , q) , (c , d)

          to-from : (a : Σ (Σ I (γ P)) (Idx (InducedOver F Q)))
            → to (from a) == a
          to-from ((i , c) , (q , d)) = idp

          from-to : (b : Σ (Σ I (Idx Q)) (γ (ΣPoly Q)))
            → from (to b) == b
          from-to ((i , q) , (c , d)) = idp
          
  -- And then the claim seems clear:
  claim : {I : Type₀} {P : Poly I} (F : FillingFamily P)
    → (Q : PolyOver P)
    → (ΣPoly Q // PbFam F Q) == ΣPoly (InducedOver F Q) [ Poly ↓ ua (IdxEquiv F Q) ]
  claim F Q = {!!}

  -- It would sure be nice if we would make that path
  -- come out to be definitional.  Ech.  But looks unlikely.
  
  DomInv : {I J : Type₀} (p : I == J)
    → {P : Poly I} {Q : Poly J}
    → (r : P == Q [ Poly ↓ p ])
    → PolyDomain P ≃ PolyDomain Q
  DomInv idp idp = ide (PolyDomain _)

  -- Yeah, not sure about the termination here.  Have we done something circular?
  {-# TERMINATING #-}
  PbDom : {I : Type₀} {P : Poly I} (D : PolyDomain P)
    → (Q : PolyOver P) → PolyDomain (ΣPoly Q)
  F (PbDom D Q) = PbFam (F D) Q
  H (PbDom D Q) = <– (DomInv (ua (IdxEquiv (F D) Q)) (claim (F D) Q)) (PbDom (H D) (InducedOver (F D) Q))
  
    where X : PolyDomain (ΣPoly (InducedOver (F D) Q))
          X = PbDom (H D) (InducedOver (F D) Q)
          
  -- Bingo, and then we would be able to transport along
  -- the corresponding path in the universe and we get what we
  -- want.
  
  -- Okay, here is somehow the idea:  we can consider
  --    ΣPoly Q // PbFam F Q
  -- and somehow the idea is that this can *also* be
  -- expressed as a polynomial over the filling poly.
  -- And if these constructions appropriately "commute"
  -- we should be in business.

  -- So, from here, what would be the idea?  I guess I sort
  -- of claim that, given a two stage filling family, I have a
  -- polynomial over the second stage whose constructors assert
  -- the wellformedness of the composite wrt Bd.

  Extension : {I : Type₀} {P : Poly I} (F : FillingFamily P) → Type₀
  Extension {I} {P} F = {i : I} (w : W P i) (c : γ P i) (f : Frame P w c) (x : F w c f) → Type₀

  ExtendedFamily : {I : Type₀} {P : Poly I} (Fm : FillingFamily P)
    → (E : Extension Fm)
    → FillingFamily P
  ExtendedFamily Fm E w c f = Σ (Fm w c f) (E w c f)

  ExtOver : {I : Type₀} {P : Poly I} (F : FillingFamily P)
    → Extension F → PolyOver (P // F)
  Idx (ExtOver F E) = cst ⊤
  Cns (ExtOver F E) {i , c} unit (w , f , x) = E w c f x
  Plc (ExtOver F E) {i , c} unit n unit = ⊤
  plc-contr (ExtOver F E) unit n = Σ-level Unit-level (λ _ → Unit-level)

  -- I see, and I think here again, we shoul have a kind of equivalence.
  postulate

    compat : {I : Type₀} {P : Poly I} (F : FillingFamily P) (E : Extension F)
      → ΣPoly (ExtOver F E) == P // ExtendedFamily F E [ Poly ↓ {!!} ]

    BDExtension : {I : Type₀} {P : Poly I}
      → (F₀ : FillingFamily P) (F₁ : FillingFamily (P // F₀))
      → Extension F₁

    CanExtend : {I : Type₀} {P : Poly I} (F : FillingFamily P) (E : Extension F)
      → PolyDomain (P // F) → PolyDomain (P // ExtendedFamily F E)

  -- Something like this is what you had in mind.  Except does this version skip
  -- too much? Yeah, something is fishy about this guy.  Or I'm not completely
  -- sure.  Maybe it's actually okay.  I have no idea what to do about termination ....
  {-# TERMINATING #-}
  BDDomain : {I : Type₀} {P : Poly I} (D : PolyDomain P) → PolyDomain P
  F (BDDomain {I} {P} D) = F D
  F (H (BDDomain {I} {P} D)) = ExtendedFamily (F (H D)) (BDExtension (F D) (F (H D)))
  H (H (BDDomain {I} {P} D)) = CanExtend (F (H D)) (BDExtension (F D) (F (H D))) (BDDomain (H (H D)))

  conjecture : {I : Type₀} (P : Poly I)
    → is-algebraic (H (BDDomain (TermDomain P)))
  is-fillable (conjecture P) pd = has-level-in (ctr , {!!})

    where ctr : CompositeFor (ExtendedFamily (λ {_} w c f → ⊤) (BDExtension (λ {_} w c f → ⊤) (λ {_} w c f → ⊤))) pd
          ctr = (flatten (TermFamily P) pd , flatten-frm (TermFamily P) pd , tt) , bd-frame (TermFamily P) pd , tt , {!!}

  is-coherent (conjecture P) pd = {!!}
  coh-algebraic (conjecture P) = {!!}
  
  -- So indeed, this looks very promising.  It's quite clear that I will be
  -- able to finish at least the fillable condition.  And the coherence looks
  -- pretty good as well.  Both are some sneaky path induction tricks.  The
  -- final step would be the coinductive hypothesis, and here, there is a bit
  -- of work to see if it comes out to the right form or something ..... dunno.

  -- Basically, it seems you would need to know that extending by the baez-dolan
  -- extension preserved the property of being algebraic.  Something like this.

  -- Okay, so an extension of the filling family gives us a polynomial
  -- over the filling poly.  So, now we have this idea of the baez dolan
  -- extension, which exists canonically as soon as we are two levels
  -- deep in a polynomial domain.
  record BDWitness {I : Type₀} {P : Poly I}
    (F₀ : FillingFamily P)
    (F₁ : FillingFamily (P // F₀))
    {i : I} {c : γ P i} (pd : W (P // F₀) (i , c))
    (cc : γ (P // F₀) (i , c))
    (ff : Frame (P // F₀) pd cc)
    (xx : F₁ pd cc ff) : Type₀ where
    field
      α : fst cc == flatten F₀ pd
      -- etc ....

  


  -- Okay, main idea: start with the terminal domain and
  -- "add" the equalities you want to see in order that
  -- this become a monad.

  -- So, the first thing is to show that you can "pullback"
  -- polynomial domains along an extension of their fillers.

  -- Extend₀ : {I : Type₀} {P : Poly I} (D : PolyDomain P)
  --   → (E : {i : I} (w : W P i) (c : γ P i) (f : Frame P w c) (x : (F D) w c f) → Type₀)
  --   → PolyDomain P
  -- F (Extend₀ {P = P} D E) = λ w c f → Σ ((F D) w c f) (E w c f)
  -- H (Extend₀ {P = P} D E) = {!H D !}



  -- PbFam : {I : Type₀} {P : Poly I} (Fm : FillingFamily P)
  --   (E : Extension Fm) → FillingFamily (P // Fm) → FillingFamily (P // ExtendedFamily Fm E)
  -- PbFam Fm E FF {i , c} pd (w , f , x , y) sf = FF {i , c} {!!} (w , f , x) {!!}

  -- Extend : {I : Type₀} {P : Poly I} (Fm : FillingFamily P)
  --   → (E : Extension Fm)
  --   → PolyDomain (P // Fm)
  --   → PolyDomain (P // ExtendedFamily Fm E)
  -- F (Extend Fm E D) = PbFam Fm E (F D)
  -- H (Extend {P = P} Fm E D) = {!!}

  -- -- Yeah, I guess you are going to need to be more careful.

  -- -- Hmmm.  Still not quite the right idea.

  -- -- Question: does the filling polynomial admit a map to P?
  -- -- It is clearly not cartesian, but ....

  -- -- I mean, no, it doesn't look like it.  Given a node of the
  -- -- source tree, how are we ever supposed to pick out a place
  -- -- of the target constructor?

  -- -- So what exactly am I asking here?  I'm asking that if I have
  -- -- a polynomial domain, that I can "extend" it with new information
  -- -- in the lowest dimension and that I obtain a new polynomial domain.

  -- -- Do I need to know all of the extensions at the begining?  Because
  -- -- maybe in the BD case I actually do know all this information.

  -- record DomainOver {I : Type₀} {P : Poly I} (D : PolyDomain P) : Type₁ where
  --   coinductive
  --   field
  --     E : Extension (F D)
  --     G : DomainOver (H D)

  -- open DomainOver

  -- ΣDom : {I : Type₀} {P : Poly I} (D : PolyDomain P) (X : DomainOver D) → PolyDomain P
  -- F (ΣDom D X) = λ w c f → Σ ((F D) w c f) ((E X) w c f)
  -- H (ΣDom D X) = {!ΣDom (H D) (G X)!}

  -- -- FillingFamily : {I : Type₀} → Poly I → Type₁
  -- -- FillingFamily {I} P = {i : I} (w : W P i) (c : γ P i) → Frame P w c → Type₀

  -- -- Ultimately, what is your claim?  Suppose I have a polynomial domain.

  -- -- Something : {I : Type₀} (P : Poly I) (Fm : FillingFamily P)
  -- --   → (D : PolyDomain (P // Fm))
  -- --   → PolyDomain (P // Fm)
  -- -- F (Something P Fm D) pd (w , f , x) sf = (F D) pd (w , f , x) sf × ((w , f , sf) == (flatten Fm pd , flatten-frm Fm pd , bd-frame Fm pd))
  -- -- H (Something P Fm D) = {!H D!}

  -- -- So it looks like all we're being asked for here is naturality.
  -- -- Well, 
