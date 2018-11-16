{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Substitution
open import PolyMonad
open import WPaths

module wip.NonDegen where

  module _ {ℓ} {I : Type ℓ} (P : Poly I) where

    lemma₀ : {i : I} (f g : Op P i) (ϕ₀ : Decor P f (W P))
      → Type ℓ
    lemma₀ = {!!}


  -- module _ {ℓ} {I : Type ℓ} (P : Poly I) where

  --   -- Perfect.  This was the main idea all along.
  --   lemma : {i : I} (f : Op P i) (g : Op P i)
  --     → (ϕ : Decor P f (W P)) (ψ : Decor P g (W P))
  --     → (e : nd (f , ϕ) == nd (g , ψ))
  --     → (h : Ops P) (l : (i , f) == h) (r : (i , g) == h)
  --     → inl l == inl r [ (λ x → Node P x h) ↓ e ]
  --     → l == ap (λ x → (i , x)) (fst= (–> (W=-equiv P) e)) ∙ r
  --   lemma {i} f g ϕ ψ e h l r d = step₄ ∙
  --     ap (λ y → y ∙ r) (ap-∘ (λ x → (i , x)) fst (–> (W=-equiv P) e))

  --     where weqv : (nd (f , ϕ) == nd (g , ψ)) ≃ (f , ϕ == g , ψ)
  --           weqv = W=-equiv P -- (nd (f , ϕ)) (nd (g , ψ))

  --           step₁ : inl l == inl r [ (λ x → Node P x h) ↓ <– weqv (–> weqv e) ]
  --           step₁ = transport! (λ x → inl l == inl r [ (λ x → Node P x h) ↓ x ])
  --                            (<–-inv-l weqv e) d

  --           step₂ : inl l == inl r [ (λ x → Node P (nd x) h) ↓ –> weqv e ]
  --           step₂ = ↓-ap-out (λ x → Node P x h) nd (–> weqv e) step₁

  --           step₃ : l == r [ (λ x → (i , fst x) == h) ↓ –> weqv e ]
  --           step₃ = ⊔-po-inl (–> weqv e) l r step₂

  --           step₄ : l == ap (λ x → (i , fst x)) (–> weqv e) ∙ r
  --           step₄ = ↓-app=cst-out step₃


  --   ParamEqv : {i : I} {f g : Op P i} (a : f == g)
  --     → (j : I) → Param P f j ≃ Param P g j
  --   ParamEqv idp j = ide _

  --   LeafEqv : {i : I} {u v : W P i} (a : u == v)
  --     → (j : I) → Leaf P u j ≃ Leaf P v j
  --   LeafEqv idp j = ide _

  --   -- Right, so this is the idea: a polynomial is
  --   -- non-degenerate if, given an automorphism of
  --   -- an operation, whenever the induced automorphism
  --   -- of the parameters is the identity, so is the
  --   -- automorphism.
  --   -- NonDegen : Type ℓ
  --   -- NonDegen = {i : I} (f : Op P i) (a : f == f)
  --   --   → (b : (j : I) → ParamEqv a j == ide (Param P f j))
  --   --   → a == idp

  --   -- A simpler version which implies the stronger one ...
  --   NonDegen : Type ℓ
  --   NonDegen = {i : I} (f : Op P i) (a : f == f)
  --     → (b : (j : I) (p : Param P f j) → transport (λ x → Param P x j) a p == p)
  --     → a == idp


  --   module _ (ζ : NonDegen) where

  --     -- Now suppose the polynomial is non degenerate.
  --     -- My idea is that this implies the *trees* are
  --     -- non-degenerate in a similar sense:

  --     LfNonDegen : {i : I} (w : W P i) (a : w == w)
  --       → (b : (j : I) → LeafEqv a j == ide (Leaf P w j))
  --       → a == idp
  --     LfNonDegen (lf i) a b = {!!} -- Trivial
  --     LfNonDegen (nd (f , ϕ)) a b = {!!}

  --       where f-loop : f == f
  --             f-loop = fst= (–> (W=-equiv P) a)

  --             hyp : (j : I) → ParamEqv f-loop j == ide (Param P f j)
  --             hyp j = equiv-== (λ p → {!!})

  --             -- Yes, closing in.  And why is this the case?
  --             blorp : (j : I) (p : Param P f j)
  --               → transport (λ x → Param P x j) f-loop p == p
  --             blorp j p = {!!}

  --             -- Arghh.  Perhaps this doesn't work.
  --             -- Because, like, what if the tree attached to
  --             -- p has no leaves?  More generaly, how am I
  --             -- suppose to pick a leaf to which I can apply
  --             -- the induction hypothesis?


  --     -- Maybe it works for nodes?
  --     NdNonDegen : {i : I} (w : W P i) (a : w == w)
  --       → (b : (g : Ops P) (n : Node P w g) → transport (λ x → Node P x g) a n == n)
  --       → a == idp
  --     NdNonDegen (lf i) a b = {!!} -- trivial ...
  --     NdNonDegen {i} (nd (f , ϕ)) a b = {!lemma f f ϕ ϕ a (i , f) idp idp!}

  --       where f-loop : f == f
  --             f-loop = fst= (–> (W=-equiv P) a)

  --             have : transport (λ x → Node P x (i , f)) a (inl idp) == inl idp
  --             have = b (i , f) (inl idp)

  --             -- we're in the same situation:
  --             canprove : Path {A = Path {A = Ops P} (i , f) (i , f)} idp (ap (λ x → i , x) f-loop)
  --             canprove = {!!}

  --             -- Can you prove this?
  --             hyp : (j : I) (p : Param P f j)
  --               → transport (λ x → Param P x j) f-loop p == p
  --             hyp j p = {!!}

  --     -- Again, for a given p, why should we have a node of ϕ j p
  --     -- to apply the assumption to?

  --     -- Yeah, so this looks like a classic problem you've had with
  --     -- understanding automorphisms of trees.  But is it stated
  --     -- differently here?

  --     -- And it seems we reach the same impass: this long standing question
  --     -- of whether trees are faithfull represented by families of
  --     -- automorphisms of their nodes...
