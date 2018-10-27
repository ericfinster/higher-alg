{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import WPaths

module Automorphisms {ℓ} {I : Type ℓ} (P : Poly I) where

  -- A duplicate from the Uniqueness file, but just for playing with.
  comp-lemma : {i : I} (f : Op P i) (g : Op P i)
    → (ϕ : Decor P f (W P)) (ψ : Decor P g (W P))
    → (e : nd (f , ϕ) == nd (g , ψ))
    → (h : Ops P) (l : (i , f) == h) (r : (i , g) == h)
    → inl l == inl r [ (λ x → Node P x h) ↓ e ]
    → l == ap (λ x → (i , x)) (fst= (–> (W=-eqv P (nd (f , ϕ)) (nd (g , ψ))) e)) ∙ r
  comp-lemma {i} f g ϕ ψ e h l r d = step₄ ∙
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

  -- Okay, idea is something like the following.

  -- Yes, yes, this is all looking kind of interesting.
  -- Can you rephrase and consolidate?  Because it looks like
  -- what is happening is that you are using node equivlences
  -- as a kind of codes fibration.

  -- On the other hand, you know that an equivalence between
  -- node spaces is not enough to determine a tree.

  NodeEqv : {i : I} (w₀ w₁ : W P i) → Type ℓ
  NodeEqv w₀ w₁ = (g : Ops P) → Node P w₀ g ≃ Node P w₁ g

  -- But we do have this map.
  embed : {i : I} (w₀ w₁ : W P i) (e : w₀ == w₁) → NodeEqv w₀ w₁
  embed w .w idp g = ide _

  -- And so it feels like what you are trying to say is that
  -- this map is monic.  Is that right?

  ↓-NodeEqv-out : {i : I} (w₀ w₁ w₂ : W P i) (e : w₁ == w₂)
    → (α : NodeEqv w₀ w₁) (β : NodeEqv w₀ w₂)
    → α == β [ NodeEqv w₀ ↓ e ]
    → (g : Ops P) (n : Node P w₀ g)
    → –> (α g) n == –> (β g) n [ (λ x → Node P x g) ↓ e ]
  ↓-NodeEqv-out w₀ w₁ .w₁ idp α .α idp g n = idp

  IdEqv : {i : I} (w : W P i) → NodeEqv w w
  IdEqv w g = ide _

  -- Uh, yeah, so why not just state it as you mean it.
  unique-fst : {i : I} (w : W P i)
    → (e : w == w)
    → (r : IdEqv w == IdEqv w [ NodeEqv w ↓ e ])
    → e == idp
  unique-fst (lf i) e r = contr-has-all-paths ⦃ lf-eq-contr P i ⦄ e idp 
  unique-fst {i} (nd (f , ϕ)) e r = {!!}

    where po : inl idp == inl idp [ (λ x → Node P x (i , f)) ↓ e ]
          po = ↓-NodeEqv-out (nd (f , ϕ)) (nd (f , ϕ)) (nd (f , ϕ)) e
                             (IdEqv (nd (f , ϕ))) (IdEqv (nd (f , ϕ)))
                              r (i , f) (inl idp)
          
          f-loop : f == f
          f-loop = fst= (–> (W=-eqv P (nd (f , ϕ)) (nd (f , ϕ))) e) 

          and-so : idp == ap (λ x → (i , x)) f-loop ∙ idp
          and-so = comp-lemma f f ϕ ϕ e (i , f) idp idp po

          -- This should be relatively straigtforward now ...
          claim : f-loop == idp
          claim = {!!}

          but-then : (j : I) (p : Param P f j) → ϕ j p == ϕ j p
          but-then j p = {!snd= (–> (W=-eqv P (nd (f , ϕ)) (nd (f , ϕ))) e)!}

          ih : (j : I) (p : Param P f j) → but-then j p == idp
          ih j p = unique-fst (ϕ j p) (but-then j p) {!!}

          -- So you transport along the null-homotopy of f-loop to
          -- get a path over the identity path, i.e. a path ϕ == ϕ.
          -- Then simply app= the parameters ...

          -- Right.  And so that will get you the first argument.
          -- But then you also need the second.  Where does that
          -- come from?

          -- Well, you have the dual to NodeEqv-out, i.e. NodeEqv-in.
          -- And for this, you'll have a certain diagram to check commutes.

          -- Finally, transporting r along the proven equality should result
          -- in the identity map.  Interesting.

          -- Well, shit.  Is this whole thing a lie?
