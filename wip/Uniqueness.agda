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

  BdFrame : {i : I} {f : Op P i} (pd : W Subst (i , f)) (w : W P i) → Type ℓ
  BdFrame pd w = (g : Ops P) → Leaf Subst pd g ≃ Node P w g

  ↓-BdFrame-out : {i : I} {f : Op P i} (pd : W Subst (i , f))
    → {w₀ w₁ : W P i} (e : w₀ == w₁)
    → (α : BdFrame pd w₀) (β : BdFrame pd w₁)
    → α == β [ BdFrame pd ↓ e ]
    → (g : Ops P) (l : Leaf Subst pd g)
    → –> (α g) l == –> (β g) l [ (λ x → Node P x g) ↓ e ]
  ↓-BdFrame-out pd idp α .α idp g l = idp

  bd-unique₀ : {i : I} {f : Op P i} (pd : W Subst (i , f))
    → (e : Path {A = Σ (W P i) (BdFrame pd)}
                (flatn pd , bd-frm pd)
                (flatn pd , bd-frm pd))
    → e == idp
  bd-unique₀ (lf (i , f)) e = {!!}

    where po : inl idp == inl idp [ (λ x → Node P x (i , f)) ↓ (fst= e) ]
          po = ↓-BdFrame-out (lf (i , f)) (fst= e)
                 (bd-frm (lf (i , f))) (bd-frm (lf (i , f)))
                 (snd= e) (i , f) idp

          f-loop : f == f
          f-loop = fst= (–> (W=-eqv P (corolla P f) (corolla P f)) (fst= e))

          and-so : idp == ap (λ x → (i , x)) f-loop ∙ idp
          and-so = lemma f f (λ j p → lf j) (λ j p → lf j) (fst= e) (i , f) idp idp po


  bd-unique₀ (nd ((w , α) , κ)) e = {!!}

    where ih-data : (g : Ops P) (n : Node P w g)
                      → Path {A = Σ (W P (fst g)) (BdFrame (κ g n))}
                          (flatn (κ g n) , bd-frm (κ g n))
                          (flatn (κ g n) , bd-frm (κ g n))
          ih-data g n = pair= {!!} {!!}

  -- So, the point is that (fst= e) gives us an equality between
  -- substituted trees.  And what we need to know is that a path
  -- between substituted trees induces (and hopefully is equivalent to...)
  -- a collection of automorphisms and so on.
  


  -- Right, so the following version asks in addition for a null homotopy of
  -- the flatn-frm.  But this I do not see immediately why it should exist.
  -- Since the result I'm interested in can be stated without it, I will
  -- try that.  I don't know if this will turn out to be a problem for the
  -- inductive step.

  -- bd-unique : {i : I} {f : Op P i} (pd : W Subst (i , f))
  --   → (e : Path {A = Σ (Op Subst (i , f)) (Frame Subst pd)}
  --     ((flatn pd , flatn-frm pd) , bd-frm pd)
  --     ((flatn pd , flatn-frm pd) , bd-frm pd))
  --   → e == idp
  -- bd-unique (lf (i , f)) e =
  --   e =⟨ pair=-η e ⟩
  --   pair= (fst= e) (snd= e) =⟨ {!fst= e!} ⟩ 
  --   idp ∎

  --   where my-po : PathOver (λ x → Node P (fst x) (i , f)) (fst= e) (inl idp) (inl idp)
  --         my-po = ↓-Op-Frame-out Subst (lf (i , f)) (fst= e)
  --                                (bd-frm (lf (i , f)))
  --                                (bd-frm (lf (i , f)))
  --                                (snd= e) (i , f) idp

  --         my-po' : PathOver (λ x → Node P x (i , f)) (fst= (fst= e)) (inl idp) (inl idp)
  --         my-po' = ↓-ap-in (λ x → Node P x (i , f)) fst my-po

  --         f-loop : f == f
  --         f-loop = fst= (–> (W=-eqv P (corolla P f) (corolla P f)) (fst= (fst= e)))

  --         d-loop : (λ j p → lf j) == (λ j p → lf j) [ (λ x → Decor P x (W P)) ↓ f-loop ]
  --         d-loop = snd= (–> (W=-eqv P (corolla P f) (corolla P f)) (fst= (fst= e)))

  --         -- And so we need to show, then, that transporting along the null homotopy
  --         -- of f-loop obtained from the next lemma, d-loop is transported to the
  --         -- identity automorphism.  And this, in some sense is completely clear:
  --         -- the given decoration ignores the data on f, a property that you have
  --         -- contemplated before.

  --         and-so : idp == ap (λ x → (i , x)) f-loop ∙ idp
  --         and-so = lemma f f (λ j p → lf j) (λ j p → lf j) (fst= (fst= e)) (i , f) idp idp my-po'
          
  -- bd-unique (nd ((w , α) , κ)) e = {!!}
