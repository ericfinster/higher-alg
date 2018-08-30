{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Substitution

module SubstCoh {I : Type₀} {P : Poly I} (R : Relator P) where

    -- Substituting a trivial decoration
    -- gives back the tree
    substitute-unit : {i : I} (w : W P i)
      → substitute R w (λ ic n → lf ic) == w
    substitute-unit (lf i) = idp
    substitute-unit (nd (f , ϕ)) =
      ap (λ x → nd (f , x)) (λ= (λ j → λ= (λ p → substitute-unit (ϕ j p))))


    -- Okay, I'm going to try to describe the relationhip that I think
    -- I am being asked for: given a leaf of substitute w and
    -- a leaf of w, if they are related by a path over the unit map,
    -- then applying the substitute leaf map to one gives the other.
    
    -- substitute-lf-to : {i : I} (w : W P i)
    --   → (κ : (c : Σ I (Op P)) → Node P w (snd c) → W (P // R) c)
    --   → (j : I) → Leaf P (substitute w κ) j → Leaf P w j

    substitute-unit-lf-to : {i : I} (w : W P i)
      → (j : I) (l₀ : Leaf P (substitute R w (λ ic n → lf ic)) j) (l₁ : Leaf P w j)
      → l₀ == l₁ [ (λ x → Leaf P x j) ↓ substitute-unit w ]
      → substitute-lf-to R w (λ ic n → lf ic) j l₀ == l₁
    substitute-unit-lf-to (lf i) .i idp idp idp = idp
    substitute-unit-lf-to (nd (f , ϕ)) j (i₀ , p₀ , l₀) (i₁ , p₁ , l₁) q =
      {!!}

    -- Okay, exactly.  And I think this will finish things off down below.
    -- Just have to massage everything into the correct form.

    -- Yeah, I still don't get it.  There doesn't seem to be an induction
    -- hypothesis, since we don't expect a frame from a fixed branch to g.
    -- So wtf?
    substitute-unit-frm-aux : {i : I} (w : W P i)
      → (g : Op P i) (α : Frame P w g) (r : R w g α)
      → ∀ j 
      → (l₀ : Leaf P (substitute R w (λ ic n → lf ic)) j)
      → (l₁ : Leaf P w j)
      → (q : l₀ == l₁ [ (λ x → Leaf P x j) ↓ substitute-unit w ])
      → flatten-frm-to R (corolla (P // R) (w , α , r)) j l₀ == –> (α j) l₁ 
    substitute-unit-frm-aux (lf i) g α r .i idp .idp idp = idp
    substitute-unit-frm-aux (nd (f , ϕ)) g α r j (i₀ , p₀ , l₀) (i₁ , p₁ , l₁) q =
      ap (fst (α j)) (pair= i₀==i₁ (↓-Σ-in {!!} {!↓-Σ-snd (↓-Σ-snd po)!}))

      where po : (i₀ , p₀ , l₀) == (i₁ , p₁ , l₁) [ (λ x → Leaf P (nd (f , x)) j) ↓  (λ= (λ j₁ → λ= (λ p → substitute-unit (ϕ j₁ p)))) ]
            po = ↓-ap-out (λ x → Leaf P x j) (λ x → nd (f , x)) (λ= (λ j₁ → λ= (λ p → substitute-unit (ϕ j₁ p)))) q

            i₀==i₁ : i₀ == i₁
            i₀==i₁ = ↓-cst-out (↓-Σ-fst po)

            p₀==p₁ : p₀ == p₁ [ (λ z → Param P f (snd z)) ↓ (pair= (λ= (λ j₁ → λ= (λ p → substitute-unit (ϕ j₁ p)))) (↓-Σ-fst po)) ]
            p₀==p₁ = ↓-Σ-fst (↓-Σ-snd po)

    substitute-unit-frm : {i : I} (w : W P i)
      → (g : Op P i) (α : Frame P w g) (r : R w g α)
      → flatten-frm R (corolla (P // R) (w , α , r)) == α [ (λ w' → Frame P w' {!(flatten R (corolla (P // R) (w , α , r)))!}) ↓ substitute-unit w ]
    substitute-unit-frm (lf i) g α r = λ= (λ j → equiv-== (λ { idp → idp }))
    substitute-unit-frm (nd (f , ϕ)) g α r =
      ↓-ap-in (λ w' → Frame P w' g) (λ x → nd (f , x))
        (↓-Π-in (λ {j} {k} q → ↓-equiv-in (λ { (i₀ , p₀ , l₀) (i₁ , p₁ , l₁) q' → {!!} })))

    -- So, uh, yeah, I think we need to use the induction hypothesis.
    -- But how exactly does one do this?

    -- Yeah, that's what I don't understand. For the induction hypothesis,
    -- I would need a frame from some branch of w to g.  But there's isn't
    -- such a thing in general.

    -- fst (α j) (i₀ , p₀ , substitute-lf-to (λ {;i₁} → R) (ϕ i₀ p₀) (λ ic n → lf ic) j l₀)
    -- fst (α k) (i₁ , p₁ , l₁)
