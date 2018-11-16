{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Substitution
open import PolyMonad
open import WPaths

module SubstMonad where

  module _ {ℓ} {I : Type ℓ} (P : Poly I) where

    TrivRel : PolyRel P
    TrivRel _ _ = Lift ⊤
  
    SubstInv : SubInvar TrivRel
    SubstInv _ = lift tt

    SubstPoly : Poly (Ops P)
    SubstPoly = P // TrivRel

    SubstMgm : PolyMagma SubstPoly
    SubstMgm = SlcMgm SubstInv

    TR = TrivRel
    SR = MgmRel SubstMgm

    postulate

      Ψ-sub : SubInvar SR

    Ext : SubInvar (MgmRel SubstMgm)
    Ext {(i , f) , ((w , α) , lift tt)} coh = result

      where result : ((flatn TR (flatn SR coh) , flatn-frm TR (flatn SR coh)) , lift tt) , bd-frm TR (flatn SR coh) ==
                     ((w , α) , lift tt) , flatn-frm SR coh
            result = Ψ-sub coh

    -- Okay, like, very rough idea: use this idea that, on leaves, the baez-dolan
    -- frame acts like the identity.  So if you have a path and a compatibility
    -- of the path so if you have a map of tree compatible with it, then you get
    -- a kind of equation.

    -- My idea was that, in the current case, perhaps the extra dimension
    -- separation sufficed to get a better equation, but I don't quite see
    -- it .....

    -- The reason that argument never seemed to go anywhere is that I couldn't
    -- see how to force the loop *itself* the be contractible.  Rather, it only
    -- seemed to be contractible in the total space of all operations, and I don't
    -- think in general this suffices ....

    -- Does the extra dimension help for some reason?

    -- So I can clearly prove that the induced automorphism of
    -- the complete tuple ((i , f) , ((w , α) , lift tt)) is
    -- trivial.  Could that be the additional wrigle room?  The fact that
    -- now I have more information on this space of pairs?  Because now
    -- the index is in some sense *tied* to the parameter via α.  So
    -- the idea would be to prove that, in this case, I *can* cancel
    -- out of the pair.  Plus, I have the extra information that the
    -- automorphism preserves the baez-dolan frame one dimension down.

    rigidity : {i : I} {f : Op P i}
      → (w : W P i) (α : Frame P w f)
      → (coh : W (SubstPoly // SR) ((i , f) , ((w , α) , lift tt)))
      → (e : flatn TR (flatn SR coh) == flatn TR (flatn SR coh))
      → e == idp
    rigidity w α (lf .((_ , _) , ((w , α) , lift tt))) e = {!!}
    rigidity w α (nd x) e = {!!}
    -- rigidity (lf i) α (lf .((i , _) , (lf i , α) , lift tt)) e =
    --   contr-has-all-paths ⦃ equiv-preserves-level ((W=-equiv P)⁻¹) ⦄ e idp
    -- rigidity (nd (f , ϕ)) α (lf .((_ , _) , (nd (f , ϕ) , α) , lift tt)) e = {!!}
    -- rigidity w α (nd x) e = {!!}
    
  -- -- rigidity {i} {f} w α (lf .((i , f) , w , α)) e = {!e!}

  -- --   where lem : idp == ap (λ z → flatn P z , flatn-frm P z) (fst= e)
  -- --         lem = anti-whisker-right (snd (μ SlcMgm (lf ((i , f) , w , α))))
  -- --                 (↓-app=cst-out (snd= e))


    -- SubInvar : Type ℓ
    -- SubInvar = {f : Ops P} (pd : W (P // R) f) → R f (flatn pd , flatn-frm pd)


  -- The relation induced by a magma
  -- MgmRel : ∀ {ℓ} {I : Type ℓ} {P : Poly I} (M : PolyMagma P) → PolyRel P
  -- MgmRel {P = P} M {i , f} (w , α) = Path {A = OutFrame P w}
  --   (μ M w , μ-frm M w) (f , α)


    -- Exactly.  So this is what you have called the "globularity condition"
    -- previously.  And so you should be able to prove it by showing the
    -- generating conditions you have been working on.  As expected.

    -- And now I am coming to think that what you have meant by "rigidity"
    -- in the past is really the same thing as saying that this proof is
    -- unique.  I.e., the space of extensions is contractible.
    -- And I believe I can see how this implies the generalized monotonicity
    -- conjecture as well as just, directly, the coherent structure of the
    -- universe.

    -- And when you see these as globularity relations, you are just saying
    -- that the proofs of globularity are unique.

    -- So, do you have any idea how to prove this?
  
    -- I think it suffices to show the automorphisms of the source are
    -- contractible.  This implies that the path space above is a proposition.
    -- But then, since it is inhabited by the proof of associativity,
    -- it is contractible.

    -- 
