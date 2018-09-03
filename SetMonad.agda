{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Substitution
open import SubstCoh
open import PolyMonad

module SetMonad where

  -- So I'm pretty sure that I've proved this before,
  -- but is there a direct way to see it?
  postulate
  
    right-cancel : ∀ {i j n} (A : Type i) (B : A → Type j)
      → has-level n (Σ A B)
      → has-level (S n) A
      → (a : A) → has-level n (B a)

  record PolyMagma {ℓ} {I : Type ℓ} (P : Poly I) : Type ℓ where
    field

      mult : {i : I} (w : W P i) → Op P i
      mult-frm : {i : I} (w : W P i) → Frame P w (mult w)

  open PolyMagma

  -- Phew.  Saved your ass here!!!
  magma-leaves-are-sets : ∀ {ℓ} {I : Type ℓ} (P : Poly I) (M : PolyMagma P)
    → (p-is-set : {i : I} (f : Op P i) (j : I) → is-set (Param P f j))
    → {i : I} (w : W P i) (j : I)
    → is-set (Leaf P w j)
  magma-leaves-are-sets P M p-is-set w j =
    equiv-preserves-level ((mult-frm M w j)⁻¹) ⦃ p-is-set (mult M w) j  ⦄

  magma-frames-are-sets : ∀ {ℓ} {I : Type ℓ} (P : Poly I) (M : PolyMagma P)
    → (p-is-set : {i : I} (f : Op P i) (j : I) → is-set (Param P f j))
    → {i : I} (w : W P i) (f : Op P i)
    → is-set (Frame P w f)
  magma-frames-are-sets P M p-is-set w f =
    Π-level (λ j → ≃-level (magma-leaves-are-sets P M p-is-set w j) (p-is-set f j))

  magma-relator : ∀ {ℓ} {I : Type ℓ} (P : Poly I) (M : PolyMagma P) → Relator P
  magma-relator P M w f α = (mult M w , mult-frm M w) == (f , α) 

  --
  --  Or definition of a set-level monad.
  --
  
  record SetMonad {ℓ} {I : Type ℓ} (P : Poly I) : Type ℓ where
    field

      sort-is-gpd : is-gpd I
      ops-is-set : is-set (Σ I (Op P))
      params-is-set : {i : I} (f : Op P i)
        → is-set (Σ I (Param P f))

      mag : PolyMagma P

      -- So is this it?  Is this what you wanted?
      laws : {i : I} (f : Op P i) (c : W (P // magma-relator P mag) (i , f))
        → magma-relator P mag (flatten (magma-relator P mag) c) f (flatten-frm (magma-relator P mag) c)

  open SetMonad

  module _ {ℓ} {I : Type ℓ} (P : Poly I) (M : SetMonad P) where

    op-fib-is-set : (i : I) → is-set (Op P i)
    op-fib-is-set = right-cancel I (Op P) (ops-is-set M) (sort-is-gpd M)
    
    param-fib-is-set : {i : I} (f : Op P i) (j : I) → is-set (Param P f j)
    param-fib-is-set f = right-cancel I (Param P f) (params-is-set M f) (sort-is-gpd M)

    -- Idea is clear: from a set monad, pass to the canonical fillers given
    -- by the identity types and show that this is again a set monad.

    MR : Relator P
    MR = magma-relator P (mag M)

    mnd-rel-has-composites : {i : I} (w : W P i)
      → is-contr (CompositeFor MR w)
    mnd-rel-has-composites w = has-level-in (ctr , pth)

      where ctr : CompositeFor MR w
            ctr = mult (mag M) w , mult-frm (mag M) w , idp

            pth : (cmp : CompositeFor MR w) → ctr == cmp
            pth (._ , ._ , idp) = idp

    HomPoly : Poly (Σ I (Op P))
    HomPoly = P // MR

    -- Phew, nice!  And even more is true: the values of the relator
    -- are in fact propositions.
    hom-op-is-set : {i : I} (f : Op P i) → is-set (Op HomPoly (i , f))
    hom-op-is-set {i} f = Σ-level (W-level P op-fib-is-set i) (λ w →
      Σ-level (magma-frames-are-sets P (mag M) param-fib-is-set w f) (λ α →
        =-preserves-level (Σ-level (op-fib-is-set i)
          (magma-frames-are-sets P (mag M) param-fib-is-set w))))

    hom-mult : {i : I} (f : Op P i) → W HomPoly (i , f) → Op HomPoly (i , f)
    hom-mult f w = flatten MR w  , flatten-frm MR w , laws M f w

    hom-mult-frm : {i : I} (f : Op P i)
      → (w : W HomPoly (i , f))
      → Frame HomPoly w (hom-mult f w)
    hom-mult-frm f w = bd-frame MR w

    -- Right.  It's interesting to note that our setup here gives exactly the
    -- canonical family, right?  Well, close.  It's the version where we have
    -- a function computing the element.

    HomMult : PolyMagma HomPoly
    mult HomMult {i , f} = hom-mult f
    mult-frm HomMult {i , f} = hom-mult-frm f

    hom-laws : {i : I} (f : Op P i)
      → (t : Op HomPoly (i , f))
        (c : W (HomPoly // magma-relator HomPoly HomMult) ((i , f) , t)) →
        magma-relator HomPoly HomMult
          (flatten (magma-relator HomPoly HomMult) c) t
          (flatten-frm (magma-relator HomPoly HomMult) c)
    hom-laws {i} ._ (w , ._ , idp) t = pair= (pair= {!!} {!!}) {!!}

    -- So, this is looking quite good.  The first is our globularity
    -- condition, which it seems to be is going to be tedious but
    -- obviously doable.  The second is a pathover in a fibration of
    -- propositions and thus trivially fillable.

    -- To see that this is a fibration of props note that, we have
    -- already shown that there are unique composites.  This means
    -- that the sum of a frame and element is equivalent to paths
    -- between the composite.  But since we are working at h-level 0,
    -- this is a path space in a set and therefore a proposition.

    -- Hence, it seems that the only thing left is the final identification
    -- with the Baez-Dolan frame.  And this, it seems, will indeed take
    -- a bit of work.

    HomMnd : SetMonad HomPoly
    sort-is-gpd HomMnd = raise-level _ (ops-is-set M)
    ops-is-set HomMnd = Σ-level (ops-is-set M) (λ { (i , f) → hom-op-is-set f })
    params-is-set HomMnd (w , α , r) = Σ-level (ops-is-set M)
      (λ { (i , f) → Node-level P (sort-is-gpd M) op-fib-is-set (params-is-set M) w f })
    mag HomMnd = HomMult
    laws HomMnd {i , f} = hom-laws f

  -- Okay, so we get a domain from the above definitions.
  MndDomain : ∀ {ℓ} {I : Type ℓ} (P : Poly I) (M : SetMonad P) → Domain P
  Rl (MndDomain P M) = MR P M
  Dm (MndDomain P M) = MndDomain (HomPoly P M) (HomMnd P M)

  module _ {ℓ} {I : Type ℓ} (P : Poly I) (M : SetMonad P)
    {i : I} {f : Op P i} (pd : W (P // MR P M) (i , f)) where

    coh-from : CompositeFor (MR (HomPoly P M) (HomMnd P M)) pd → CoherenceFor (MR (HomPoly P M) (HomMnd P M)) pd
    coh-from ((._ , ._ , ._) , ._ , idp) = laws M _ pd , idp

    coh-to-from : (cmp : CompositeFor (MR (HomPoly P M) (HomMnd P M)) pd)
      → coh-to-comp (MR (HomPoly P M) (HomMnd P M)) pd (coh-from cmp) == cmp
    coh-to-from ((._ , ._ , ._) , ._ , idp) = idp

    -- This should follow immediately from the fact that the type of
    -- coherences is a proposition in the case at hand.
    coh-from-to : (coh : CoherenceFor (MR (HomPoly P M) (HomMnd P M)) pd)
      → coh-from (coh-to-comp (MR (HomPoly P M) (HomMnd P M)) pd coh) == coh
    coh-from-to coh = {!!}

    mnd-rel-is-coherent : is-equiv (coh-to-comp (MR (HomPoly P M) (HomMnd P M)) pd)
    mnd-rel-is-coherent =
      is-eq (coh-to-comp (MR (HomPoly P M) (HomMnd P M)) pd)
            coh-from coh-to-from coh-from-to

  is-algebraic-mnd-domain : ∀ {ℓ} {I : Type ℓ} (P : Poly I) (M : SetMonad P)
    → is-algebraic (MndDomain P M)
  is-fillable (is-algebraic-mnd-domain P M) = mnd-rel-has-composites P M
  is-coherent (is-algebraic-mnd-domain P M) = mnd-rel-is-coherent P M
  coh-algebraic (is-algebraic-mnd-domain P M) = is-algebraic-mnd-domain (HomPoly P M) (HomMnd P M)
