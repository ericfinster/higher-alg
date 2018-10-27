{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import WPaths

module Corolla {ℓ} {I : Type ℓ} (P : Poly I) where

  -- Okay, first we extract the base, not from the witness
  -- of contractibility, but from the tree itself.

  is-corolla : {i : I} → W P i → Type ℓ
  is-corolla w = is-contr (Σ (Ops P) (Node P w))

  corolla-dec-unique : {i : I} (f : Op P i)
    → (ϕ : Decor P f (W P))
    → is-corolla (nd (f , ϕ))
    → ϕ == (λ j _ → lf j)
  corolla-dec-unique f ϕ is-c = {!!}

  -- This can be weakened: we only need that the space of nodes is *non-empty*
  base-op : {i : I} → Σ (W P i) is-corolla → Op P i
  base-op (lf i , is-cor) = ⊥-rec (lower (snd (contr-center is-cor)))
  base-op (nd (f , _) , _) = f

  to-corolla : {i : I} (f : Op P i) → Σ (W P i) is-corolla
  to-corolla {i} f = corolla P f , has-level-in (ctr , pth)

    where ctr : Σ (Ops P) (Node P (corolla P f))
          ctr = ((i , f) , inl idp)

          pth : (n : Σ (Ops P) (Node P (corolla P f))) → ctr == n
          pth (.(i , f) , inl idp) = idp
          pth (_ , inr (_ , _ , ()))

  base-op-is-equiv : {i : I} → is-equiv (base-op {i})
  base-op-is-equiv {i} = is-eq (base-op {i}) to-corolla (λ _ → idp) lem

    where lem : (c : Σ (W P i) is-corolla) → to-corolla (base-op c) == c
          lem (lf i , is-c) = ⊥-rec (lower (snd (contr-center is-c)))
          lem (nd (f , ϕ) , is-c) = pair= (ap (λ x → nd (f , x)) (! (corolla-dec-unique f ϕ is-c))) {!!}
                                          -- (prop-has-all-paths-↓ {B = is-corolla} {p = (ap (λ x → nd (f , x)) (! (corolla-dec-unique f ϕ is-c)))} ⦃ is-contr-is-prop ⦄) 

  -- Cool. So this is clearly going to work.
  -- Yep.  Looks fine.

  -- So, the next idea is to generalize this so as to obtain the conjecture
  -- that you thought should be true from the very beginning: an equivalence
  -- which preserves the height of nodes is an equality.
