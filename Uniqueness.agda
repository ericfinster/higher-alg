{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import WPaths

module Uniqueness {ℓ} {I : Type ℓ} (P : Poly I) where

  corolla-nd-eqv : {i : I} (f : Op P i) {g : Ops P}
    → Node P (corolla P f) g ≃ ((i , f) == g)
  corolla-nd-eqv {i} f {j , g} = equiv
    (λ { (inl e) → e ;
         (inr (i , p , ())) }) inl
    (λ b → idp)
    (λ { (inl e) → idp ;
         (inr (i , p , ())) })

  corolla-pth-to : {i : I} (f : Op P i) (g : Op P i)
    → f == g
    → corolla P f == corolla P g
  corolla-pth-to f g = ap (corolla P)

  corolla-pth-to-lem : {i : I} (f : Op P i) (g : Op P i)
    → (e : f == g) 
    → corolla-pth-to f g e == <– (W=-eqv P (corolla P f) (corolla P g)) (e , {!!})
  corolla-pth-to-lem f .f idp = {!idp!}

  -- In fact, this is part of an equivalence.
  corolla-pth-from : {i : I} (f : Op P i) (g : Op P i)
    → corolla P f == corolla P g
    → f == g
  corolla-pth-from f g e = fst (–> (W=-eqv P (corolla P f) (corolla P g)) e)

  -- Hmmm.  Yikes.  So maybe you were too quick here:
  -- The automorphisms of a corolla might also be induced
  -- by non-trivial homotopies in the space of sorts I.

  -- Imagine, for example, an operation with a single input.
  -- Then even fixing this input, the corolla obtains an
  -- automorphism from tracing a loop inside the space of
  -- sorts.

  -- On the other hand, I do not think this actually is
  -- a problem for what you wanted to prove here: 
  -- I still believe that the action on a node is
  -- given by transport along the path given by projecting
  -- out the first factor.  But the reason is not exactly clear ...

  corolla-pth-equiv : {i : I} (f : Op P i) (g : Op P i)
    → (corolla P f == corolla P g)
    ≃ Σ (f == g) (λ e → Decor= P (W P) e (λ j p → lf j) (λ j p → lf j))
  corolla-pth-equiv f g = W=-eqv P (corolla P f) (corolla P g)

  -- Right, here is a first example.
  corolla-lem₀ : {i : I} (f : Op P i) (g : Op P i)
    → (e : f == g) (h : Ops P)
    → (m : (i , f) == h) (n : (i , g) == h)
    → inl m == inl n [ (λ x → Node P (corolla P x) h) ↓ e ]
    → m == n [ (λ x → x == h) ↓ pair= idp e ]
  corolla-lem₀ f .f idp h m n d = fst (inl=inl-equiv m n) d

  -- Bingo, so here's you lemma.  Probably this is even an equivalence ...
  module _ {A : Type ℓ} {B : Type ℓ} (C : B → Type ℓ) (f : A → B)
    (ap-eqv : (x y : A) → is-equiv (ap f {x} {y})) where

    -- And what's the claim?
    ap-eqv-lem : {x y : A} {p : f x == f y} {u : C (f x)} {v : C (f y)}
      → u == v [ C ↓ p ]
      → u == v [ C ∘ f ↓ is-equiv.g (ap-eqv x y) p ]
    ap-eqv-lem {x} {y} {p} {u} {v} q = ↓-ap-out C f (is-equiv.g (ap-eqv x y) p)
      (transport! (λ r → u == v [ C ↓ r ]) (is-equiv.f-g (ap-eqv x y) p) q)


  -- corolla-nd-extract : {i : I} (f : Op P i) 
  --   → {g : Ops P}
  --   → Node P (corolla P f) g → (i , f) == g
  -- corolla-nd-extract f {j , g} = {!!}

  -- corolla-po-extract₀ : {i : I} (f : Op P i) (g : Op P i)
  --   → (e : corolla P f == corolla P g)
  --   → (j : I) (h : Op P j)
  --   → (a : (i , f) == (j , h)) (b : (i , g) == (j , h))
  --   → inl a == inl b [ (λ x → Node P x (j , h)) ↓ e ]
  --   → inl a == inl b [ (λ x → Node P (corolla P x) (j , h)) ↓ corolla-pth f g e ]
  -- corolla-po-extract₀ f g e j h a b d = {!!}

  corolla-po-extract : {i : I} (f : Op P i) (g : Op P i)
    → (e : corolla P f == corolla P g)
    → (j : I) (h : Op P j)
    → (a : (i , f) == (j , h)) (b : (i , g) == (j , h))
    → inl a == inl b [ (λ x → Node P x (j , h)) ↓ e ]
    → a == b [ (λ x → x == (j , h)) ↓ pair= idp (corolla-pth-from f g e) ]
  corolla-po-extract {i} f g e j h a b d =
    ↓-ap-in (λ x → x == j , h) (λ x → i , x) {!!} 

  -- Actually, maybe this is even true more generally:
  -- if you have a *base* node, then the transport along
  -- an equality should not depend in any way on the
  -- decoration.

  -- But okay, how do I prove this?

  -- Okay, maybe I am starting to see the problem.
  -- I guess the thing is that your path space characterization
  -- doesn't use the *canonical* decomposition so that you are
  -- getting less path induction then you might like.

  -- Because, for example, if you used the canonical characterization,
  -- you could path induct on the data *equivalent* to a path between
  -- nodes, and this will actually take the form of an ap directly.
  -- And yes, then in that case you will be able to use other methods
  -- to split up the pieces.

  -- Okay, so that settles it.  You should write out the canonical
  -- characterization and use it.  In this case, your lemma above
  -- will apply directly.

  -- Okay, that's the plan.

  corolla-lem : {i : I} (f : Op P i) (g : Op P i)
    → (e : corolla P f == corolla P g)
    → (j : I) (h : Op P j)
    → (a : (i , f) == (j , h)) (b : (i , g) == (j , h))
    → inl a == inl b [ (λ x → Node P x (j , h)) ↓ e ]
    → a == pair= idp (corolla-pth-from f g e) ∙ b
  corolla-lem f g e j h a b d = {!↓-app=cst-out (corolla-po-extract f g e j h a b d)!}

  open import Substitution P

  -- Okay, let's state the uniqueness conjecture and then
  -- try to see what we need to do to prove it.

  bd-unique : {i : I} {f : Op P i} (pd : W Subst (i , f))
    → (e : Path {A = Σ (Op Subst (i , f)) (Frame Subst pd)}
      ((flatn pd , flatn-frm pd) , bd-frm pd)
      ((flatn pd , flatn-frm pd) , bd-frm pd))
    → e == idp
  bd-unique (lf (i , f)) e =
    e =⟨ pair=-η e ⟩
    pair= (fst= e) (snd= e) =⟨ {!fst= (fst= e)!} ⟩ 
    idp ∎

    where my-po : PathOver (λ x → Node P (fst x) (i , f)) (fst= e) (inl idp) (inl idp)
          my-po = ↓-Op-Frame-out Subst (lf (i , f)) (fst= e)
                                 (bd-frm (lf (i , f)))
                                 (bd-frm (lf (i , f)))
                                 (snd= e) (i , f) idp

          my-po' : PathOver (λ x → Node P x (i , f)) (fst= (fst= e)) (inl idp) (inl idp)
          my-po' = ↓-ap-in (λ x → Node P x (i , f)) fst my-po

          and-so : idp == ap (i ,_) (corolla-pth-from f f (fst= (fst= e))) ∙ idp
          and-so = corolla-lem f f (fst= (fst= e)) i f idp idp my-po'
          
  bd-unique (nd ((w , α) , κ)) e = {!!}

  -- So here we need a lemma which extracts the pathover in the path
  -- space from the node.  Then the claim is that given such a path
  -- over, we will get a commutative diagram between the identity and
  -- itself given by composition with the path extracted from the
  -- automorphism of the corolla.  Cancelling one of the identities
  -- then leaves us with the desired contraction of the first component
  -- of e.

  -- Uh, right.  So it definitely looks like your strategy is working here.
  -- At least, it appears you will indeed succeed in contracting the first
  -- component.  It remains to be seen if everything is then compatible with
  -- this contraction, but it seems extremely likely.

  -- So, what you see now is, what amounts to the identity map on the
  -- path space.  And what was your argument?

  -- Okay, good, so now we see from this setup that, as you
  -- imagined, this map is given by simply the identity map
  -- on the first factor.

  -- Then lemma, then, is that the path over obtained from
  -- e is then given by composition with the path obtained
  -- from our automorphism of the corolla.  And if this is
  -- the case, we have that this identity map is equivalent
  -- to composition with that path, which therefore must be
  -- the identity.  It seems quite clear to me that this
  -- will work ...

  -- So, for the next case, it seems our first step is to
  -- characterize the automorphisms of substitution, just as
  -- we characterized the automorphisms of the corolla.

  -- Okay, yes, and the natural conjecture is that this consists
  -- exactly of an automorphism of each of the trees being
  -- substituted, since the decoration is taken care of by the
  -- frame.

  -- If this is indeed the case, you will see that an automorphism
  -- in the inductive case is exactly an automorphism of the
  -- inductively flattened tree.

  -- And then it is natural to think that the path over will give
  -- us exactly a path over all of these automorphisms.  Applying
  -- the induction hypothesis, we should see that the function
  -- giving all of these automorphisms is equivalent to the constant
  -- function at the identity, which should itself obviously induce
  -- the identity automorphism on the substitution.

  -- I'm not entirely sure to what extent automorphisms of the
  -- flatten frame will play a role, but it looks as though a
  -- basic picture is developing: iteratively characterize the
  -- path spaces of trees obtained from substitution and grafting,
  -- then show that this characterization is sufficiently nice to
  -- apply the induction hypothesis in the above proof.
