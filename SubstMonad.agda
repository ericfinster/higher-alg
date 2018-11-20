{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Substitution
open import PolyMonad
open import Generating
open import WPaths

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

  --   subst-unit : {i : I} (w : W P i)
  --     → subst P w (λ g n → fst (subst-η g)) == w
  --   subst-unit (lf i) = idp
  --   subst-unit (nd (f , ϕ)) =
  --     ap (λ x → nd (f , x)) (λ= (λ j → λ= (λ p → subst-unit (ϕ j p))))

  --   -- So, like, for example here, if you knew that some constructors
  --   -- had automorphisms, if seems like you could just insert them
  --   -- and have a different unit map, no?

  --   -- What could possibly exclude this possibility?

  --   -- Can you exploit the fact that it is generalized by first
  --   -- evaluation on a *particular* choice of frame so as 
  --   -- to derive a relation that must hold?

  --   -- Can you use other parts of the law, like assoc or the
  --   -- *other* unit guy to derive relations?  For example, what
  --   -- does the other unit law say?

  --   -- It says that, for any operation in subst (that is, tree with
  --   -- a frame to some operation) substituting the whole shebang
  --   -- into the corolla on the output operation gives back the
  --   -- tree with its frame.

  --   -- Okay, but I do like the perspective shift of saying, okay
  --   -- lets suppose we have the laws for *all* trees.  Like a
  --   -- kind of homomorphism.  Then can we cleverly choose some trees
  --   -- or frames or whatever to see that these laws cannot be arbitrary ...
    
  --   subst-unit-unique : (u : {i : I} (w : W P i)
  --     → subst P w (λ g n → fst (subst-η g)) == w)
  --     → u == subst-unit
  --   subst-unit-unique u = λ= (λ { (lf i) → contr-has-all-paths ⦃ equiv-preserves-level ((W=-equiv P)⁻¹) ⦄ (u (lf i)) idp ;
  --                                 (nd (f , ϕ)) → {!fst= (–> (W=-equiv P) (u (nd (f , ϕ))))!} }) -- So what about this?

  --   -- So what's the point?  Well, I should be able to
  --   -- extract from u a proof that the two decorations
  --   -- are the same.  And by the induction hypothesis, this
  --   -- proof is equal to the one given by subst unit.

  --   -- and so it looks like i need to again cancel the
  --   -- loop on f that I obtain from projection.  Is there
  --   -- a reason this is possible which avoids the problems
  --   -- you were having before?

  --   -- Okay, so the first one gives the identification of the
  --   -- flatten frame with α
  
  --   subst-unit-lem : {i : I} {f : Op P i} (w : W P i) (α : Frame P w f)
  --     → (λ j → α j ∘e subst-lf-eqv P w (λ g n → fst (subst-η g)) j) ==
  --       α [ (λ x → Frame P x f) ↓ subst-unit w ]
  --   subst-unit-lem (lf i) α = λ= (λ j → equiv-== (λ l → idp ))
  --   subst-unit-lem (nd (f , ϕ)) α = {!!}

  --   subst-unit-l : {f : Ops P} (w : Op SubstPoly f) → subst-γ w (λ j _ → subst-η j) == w
  --   subst-unit-l ((w , α) , r) = pair= (pair= (subst-unit w) (subst-unit-lem w α))
  --     prop-has-all-paths-↓

  --   -- And this one will say something about the compatibility with
  --   -- the baez dolan frame.
    
  --   subst-unit-l-frm : {f : Ops P} (w : Op SubstPoly f) (g : Ops P)
  --     → (n : Param SubstPoly w g)
  --     → (–> (subst-γ-frm w (λ h _ → subst-η h) g) (g , n , –> (subst-η-frm g g) idp))
  --       == n [ (λ x → Param SubstPoly x g) ↓ subst-unit-l w ]
  --   subst-unit-l-frm = {!!}

  --   -- Okay, you should prove these two guys.
  --   -- Then the claim is that these two proofs are *unique*

  --   -- What's going to happen?


  --   -- SubstLaws : BinaryLaws SubstPoly SubstBin
  --   -- unit-l SubstLaws = subst-unit-l
  --   -- unit-l-frm SubstLaws = subst-unit-l-frm
  --   -- unit-r SubstLaws = {!!}
  --   -- unit-r-frm SubstLaws = {!!}
  --   -- assoc SubstLaws = {!!}

  --   -- SubstMgm : PolyMagma SubstPoly
  --   -- SubstMgm = SlcMgm SubstInv

  --   -- Okay, let's start writing what we need for the coherence
  --   -- structure on substitution.

  -- --   TR = TrivRel
  -- --   SR = MgmRel SubstMgm

  -- --   postulate

  -- --     Ψ-sub : SubInvar SR

  -- --   Ext : SubInvar (MgmRel SubstMgm)
  -- --   Ext {(i , f) , ((w , α) , lift tt)} coh = result

  -- --     where result : ((flatn TR (flatn SR coh) , flatn-frm TR (flatn SR coh)) , lift tt) , bd-frm TR (flatn SR coh) ==
  -- --                    ((w , α) , lift tt) , flatn-frm SR coh
  -- --           result = Ψ-sub coh

  -- --   -- Okay, like, very rough idea: use this idea that, on leaves, the baez-dolan
  -- --   -- frame acts like the identity.  So if you have a path and a compatibility
  -- --   -- of the path so if you have a map of tree compatible with it, then you get
  -- --   -- a kind of equation.

  -- --   -- My idea was that, in the current case, perhaps the extra dimension
  -- --   -- separation sufficed to get a better equation, but I don't quite see
  -- --   -- it .....

  -- --   -- The reason that argument never seemed to go anywhere is that I couldn't
  -- --   -- see how to force the loop *itself* the be contractible.  Rather, it only
  -- --   -- seemed to be contractible in the total space of all operations, and I don't
  -- --   -- think in general this suffices ....

  -- --   -- Does the extra dimension help for some reason?

  -- --   -- So I can clearly prove that the induced automorphism of
  -- --   -- the complete tuple ((i , f) , ((w , α) , lift tt)) is
  -- --   -- trivial.  Could that be the additional wrigle room?  The fact that
  -- --   -- now I have more information on this space of pairs?  Because now
  -- --   -- the index is in some sense *tied* to the parameter via α.  So
  -- --   -- the idea would be to prove that, in this case, I *can* cancel
  -- --   -- out of the pair.  Plus, I have the extra information that the
  -- --   -- automorphism preserves the baez-dolan frame one dimension down.

  -- --   rigidity : {i : I} {f : Op P i}
  -- --     → (w : W P i) (α : Frame P w f)
  -- --     → (coh : W (SubstPoly // SR) ((i , f) , ((w , α) , lift tt)))
  -- --     → (e : flatn TR (flatn SR coh) == flatn TR (flatn SR coh))
  -- --     → e == idp
  -- --   rigidity w α (lf .((_ , _) , ((w , α) , lift tt))) e = {!!}
  -- --   rigidity w α (nd x) e = {!!}
  -- --   -- rigidity (lf i) α (lf .((i , _) , (lf i , α) , lift tt)) e =
  -- --   --   contr-has-all-paths ⦃ equiv-preserves-level ((W=-equiv P)⁻¹) ⦄ e idp
  -- --   -- rigidity (nd (f , ϕ)) α (lf .((_ , _) , (nd (f , ϕ) , α) , lift tt)) e = {!!}
  -- --   -- rigidity w α (nd x) e = {!!}
    
  -- -- -- -- rigidity {i} {f} w α (lf .((i , f) , w , α)) e = {!e!}

  -- -- -- --   where lem : idp == ap (λ z → flatn P z , flatn-frm P z) (fst= e)
  -- -- -- --         lem = anti-whisker-right (snd (μ SlcMgm (lf ((i , f) , w , α))))
  -- -- -- --                 (↓-app=cst-out (snd= e))


  -- --   -- SubInvar : Type ℓ
  -- --   -- SubInvar = {f : Ops P} (pd : W (P // R) f) → R f (flatn pd , flatn-frm pd)


  -- -- -- The relation induced by a magma
  -- -- -- MgmRel : ∀ {ℓ} {I : Type ℓ} {P : Poly I} (M : PolyMagma P) → PolyRel P
  -- -- -- MgmRel {P = P} M {i , f} (w , α) = Path {A = OutFrame P w}
  -- -- --   (μ M w , μ-frm M w) (f , α)


  -- --   -- Exactly.  So this is what you have called the "globularity condition"
  -- --   -- previously.  And so you should be able to prove it by showing the
  -- --   -- generating conditions you have been working on.  As expected.

  -- --   -- And now I am coming to think that what you have meant by "rigidity"
  -- --   -- in the past is really the same thing as saying that this proof is
  -- --   -- unique.  I.e., the space of extensions is contractible.
  -- --   -- And I believe I can see how this implies the generalized monotonicity
  -- --   -- conjecture as well as just, directly, the coherent structure of the
  -- --   -- universe.

  -- --   -- And when you see these as globularity relations, you are just saying
  -- --   -- that the proofs of globularity are unique.

  -- --   -- So, do you have any idea how to prove this?
  
  -- --   -- I think it suffices to show the automorphisms of the source are
  -- --   -- contractible.  This implies that the path space above is a proposition.
  -- --   -- But then, since it is inhabited by the proof of associativity,
  -- --   -- it is contractible.

  -- --   -- 
