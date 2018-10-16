{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import WPaths

module Uniqueness {ℓ} {I : Type ℓ} (P : Poly I) where

  -- Perfect.  This was the main idea all along.
  lemma : {i : I} (f : Op P i) (g : Op P i)
    → (ϕ : Decor P f (W P)) (ψ : Decor P g (W P))
    → (e : nd (f , ϕ) == nd (g , ψ))
    → (h : Ops P) (l : (i , f) == h) (r : (i , g) == h)
    → inl l == inl r [ (λ x → Node P x h) ↓ e ]
    → l == ap (λ x → (i , x)) (fst= (–> (W=-eqv P (nd (f , ϕ)) (nd (g , ψ))) e)) ∙ r
  lemma {i} f g ϕ ψ e h l r d = step₄ ∙
    ap (λ y → y ∙ r) (ap-∘ (λ x → (i , x)) fst (–> (W=-eqv P (nd (f , ϕ)) (nd (g , ψ))) e))

    where weqv : (nd (f , ϕ) == nd (g , ψ)) ≃ (f , ϕ == g , ψ)
          weqv = W=-eqv P (nd (f , ϕ)) (nd (g , ψ))

          step₁ : inl l == inl r [ (λ x → Node P x h) ↓ <– weqv (–> weqv e) ]
          step₁ = transport! (λ x → inl l == inl r [ (λ x → Node P x h) ↓ x ])
                           (<–-inv-l weqv e) d

          step₂ : inl l == inl r [ (λ x → Node P (nd x) h) ↓ –> weqv e ]
          step₂ = ↓-ap-out (λ x → Node P x h) nd (–> weqv e) step₁

          step₃ : l == r [ (λ x → (i , fst x) == h) ↓ –> weqv e ]
          step₃ = ⊔-po-inl (–> weqv e) l r step₂

          step₄ : l == ap (λ x → (i , fst x)) (–> weqv e) ∙ r
          step₄ = ↓-app=cst-out step₃

  open import Substitution P

  bd-unique : {i : I} {f : Op P i} (pd : W Subst (i , f))
    → (e : Path {A = Σ (Op Subst (i , f)) (Frame Subst pd)}
      ((flatn pd , flatn-frm pd) , bd-frm pd)
      ((flatn pd , flatn-frm pd) , bd-frm pd))
    → e == idp
  bd-unique (lf (i , f)) e =
    e =⟨ pair=-η e ⟩
    pair= (fst= e) (snd= e) =⟨ {!!} ⟩ 
    idp ∎

    where my-po : PathOver (λ x → Node P (fst x) (i , f)) (fst= e) (inl idp) (inl idp)
          my-po = ↓-Op-Frame-out Subst (lf (i , f)) (fst= e)
                                 (bd-frm (lf (i , f)))
                                 (bd-frm (lf (i , f)))
                                 (snd= e) (i , f) idp

          my-po' : PathOver (λ x → Node P x (i , f)) (fst= (fst= e)) (inl idp) (inl idp)
          my-po' = ↓-ap-in (λ x → Node P x (i , f)) fst my-po

          and-so : idp == ap (λ x → (i , x)) (fst= (–> (W=-eqv P (corolla P f) (corolla P f)) (fst= (fst= e)))) ∙ idp
          and-so = lemma f f (λ j p → lf j) (λ j p → lf j) (fst= (fst= e)) (i , f) idp idp my-po'
          
  bd-unique (nd ((w , α) , κ)) e = {!!}

