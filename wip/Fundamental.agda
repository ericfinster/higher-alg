{-# OPTIONS --without-K --rewriting #-}

open import HoTT

--
--  My implementation of the fundamental theorem of HoTT
--

module Fundamental where

  decode : ∀ {ℓ} {X : Type ℓ} (P : X → Type ℓ) {x₀ : X} (p₀ : P x₀)
    → (x : X) → x₀ == x → P x
  decode P p₀ x q = transport P q p₀

  module _ {ℓ} (X : Type ℓ) (P : X → Type ℓ) (is-c : is-contr (Σ X P)) where

    private
    
      x₀ : X
      x₀ = fst (contr-center is-c)

      p₀ : P x₀
      p₀ = snd (contr-center is-c)

      to : (x : X) → P x → x₀ == x
      to x p = fst= (contr-path is-c (x , p))

      from : (x : X) → x₀ == x → P x
      from x q = decode P p₀ x q

      to-from : (x : X) (q : x₀ == x) → to x (from x q) == q
      to-from .x₀ idp = ap fst= lem

        where lem : contr-path is-c (x₀ , p₀) == idp
              lem = contr-has-all-paths ⦃ has-level-apply (raise-level ⟨-2⟩ is-c) (x₀ , p₀) (x₀ , p₀) ⦄
                     (contr-path is-c (x₀ , p₀)) idp 

      from-to : (x : X) (p : P x) → from x (to x p) == p
      from-to x p = to-transp (snd= (contr-path is-c (x , p)))

    ft-to : (x : X) → P x ≃ (x₀ == x)
    ft-to x = equiv (to x) (from x) (to-from x) (from-to x)

  module _ {ℓ} {X : Type ℓ} (P : X → Type ℓ) (x₀ : X) (p₀ : P x₀)
    (decode-eqv : (x : X) → is-equiv (decode P p₀ x)) where

    c-pth : (xp : Σ X P) → (x₀ , p₀) == xp
    c-pth (x , p) = pair= pth (from-transp P pth (is-equiv.f-g (decode-eqv x) p))

      where pth : x₀ == x
            pth = is-equiv.g (decode-eqv x) p

    ft-from : is-contr (Σ X P)
    ft-from = has-level-in ((x₀ , p₀) , c-pth)
