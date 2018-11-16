{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Substitution
open import PolyMonad

module wip.Monotonicity where

  -- Okay, I want to state the monotonicity conjecture.
  -- Actually, it seems we can define the notion of "n-monad".

  module _ {ℓ} {I : Type ℓ} {P : Poly I} (M : PolyMagma P) where

    R = MgmRel M

    -- The "laws" of a monad will live in this space.
    rel-space : {i : I} {f : Op P i} (pd : W (P // R) (i , f)) → Type ℓ
    rel-space {i} {f} pd =
      let w = flatn R pd
          α = flatn-frm R pd
      in Path {A = OutFrame _ w} (μ M w , μ-frm M w) (f , α)

    magma-has-level : (n : ℕ₋₂) → Type ℓ
    magma-has-level n = {i : I} {f : Op P i} (pd : W (P // R) (i , f))
      → has-level n (rel-space pd) 
  
  monotonicity : ∀ {n ℓ} {I : Type ℓ} {P : Poly I}
    → (M : PolyMagma P) (Ψ : SubInvar (MgmRel M))
    → magma-has-level M (S n)
    → magma-has-level (SlcMgm Ψ) n
  monotonicity {⟨-2⟩} M Ψ lvl {i , ._} {(w , ._) , idp} coh = has-level-in (ctr , {!!})

    where MR = MgmRel M
          SR = MgmRel (SlcMgm Ψ)

          ctr : (((flatn MR (flatn SR coh) , flatn-frm MR (flatn SR coh)) , Ψ (flatn SR coh)) , bd-frm MR (flatn SR coh)) ==
                ((w , μ-frm M w) , idp) , flatn-frm SR coh
          ctr = {!!}

  -- Okay, so let's pause here and look at the situation.
  -- Ψ, in this case, takes values in a proposition by assumption.
  -- Hence, this will not be an issue: all path overs will exist.

  -- Now, we have seen that such a path exists.
  -- You should work it out again, but I believe its existence is equivalent
  -- to the associativity of the substitution monad.

  -- What we are being asked to prove, therefore, is that this proof of
  -- associativity is *unique*.

  -- So this seems very much related to the idea that substitution and
  -- grafting have *unique* extension spaces.
  
  monotonicity {S n} M Ψ lvl {i , ._} {(w , ._) , idp} coh =
    has-level-in (λ x y → {!rel-space (SlcMgm Ψ) coh!})

  -- In summary, it feels like what you are describing as rigidity can be
  -- similary described in a couple of equivalent ways:

  --
  -- 1) The uniqueness of the extensions of substitution monads
  --    (which you expect from the universe and should be equivalent to it ...)
  --
  -- 2) The uniqueness of proofs of globularity.
  --    (because that is what you have called this equality previously)
  --

  
