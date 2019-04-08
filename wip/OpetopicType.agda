{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import PolyMonad

module wip.OpetopicType where

  --
  -- It is tempting to take the following seemingly very natural
  -- definition as that of opetopic type.  However, I do not think
  -- it is very well behaved.
  --
  --   record OpetopicType' {ℓ} {I : Type ℓ} (P : Poly I) : Type (lsucc ℓ) where
  --     coinductive
  --     field
    
  --       R : PolyRel P
  --       H : OpetopicType' (P // R)
  --
  -- Rather, one needs to incorporate the "boundary" operations given by
  -- flattening, substitution and grafting.  That is, after a single
  -- slice, we have a *canonical* choice of frame and we need to take
  -- advatage of it.
  --

  module _ {ℓ} {I : Type ℓ} (P : Poly I) (R : PolyRel P) where
  
    SliceRel : Type (lsucc ℓ)
    SliceRel = {i : I} (f : Op P i) (pd : W (P // R) (i , f))
      → R (i , f) (flatn R pd , flatn-frm R pd) → Type ℓ

    -- Yeah, and even this is not really finished: you will
    -- also need β == bd-frm.
    to-poly-rel : SliceRel → PolyRel (P // R)
    to-poly-rel Q ((i , f) , (w , α) , r) (pd , β) =
      Σ (Path {A = InFrame P (i , f)} (w , α) (flatn R pd , flatn-frm R pd)) (λ pth →
        Q f pd (transport (R (i , f)) pth r))


  record OpetopicType {ℓ} {I : Type ℓ} (P : Poly I) (R : PolyRel P) : Type (lsucc ℓ) where
    coinductive
    field

      Q : SliceRel P R
      K : OpetopicType (P // R) (to-poly-rel P R Q)


