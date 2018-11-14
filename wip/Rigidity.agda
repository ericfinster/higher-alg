{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import WPaths

module wip.Rigidity {ℓ} {I : Type ℓ} (P : Poly I) where

  -- So, like, maybe you should start with something just
  -- even more basic: suppose you have an automorphism of
  -- a tree.  Now suppose that the corresponding maps on
  -- leaves and nodes are the identity.  Is it true then
  -- that the automorphism is the identity?

  -- Perfect.  This was the main idea all along.
  lemma : {i : I} (f : Op P i) (g : Op P i)
    → (ϕ : Decor P f (W P)) (ψ : Decor P g (W P))
    → (e : nd (f , ϕ) == nd (g , ψ))
    → (h : Ops P) (l : (i , f) == h) (r : (i , g) == h)
    → inl l == inl r [ (λ x → Node P x h) ↓ e ]
    → l == ap (λ x → (i , x)) (fst= (–> (W=-equiv P) e)) ∙ r
  lemma {i} f g ϕ ψ e h l r d = step₄ ∙
    ap (λ y → y ∙ r) (ap-∘ (λ x → (i , x)) fst (–> (W=-equiv P) e))

    where weqv : (nd (f , ϕ) == nd (g , ψ)) ≃ (f , ϕ == g , ψ)
          weqv = W=-equiv P 

          step₁ : inl l == inl r [ (λ x → Node P x h) ↓ <– weqv (–> weqv e) ]
          step₁ = transport! (λ x → inl l == inl r [ (λ x → Node P x h) ↓ x ])
                           (<–-inv-l weqv e) d

          step₂ : inl l == inl r [ (λ x → Node P (nd x) h) ↓ –> weqv e ]
          step₂ = ↓-ap-out (λ x → Node P x h) nd (–> weqv e) step₁

          step₃ : l == r [ (λ x → (i , fst x) == h) ↓ –> weqv e ]
          step₃ = ⊔-po-inl (–> weqv e) l r step₂

          step₄ : l == ap (λ x → (i , fst x)) (–> weqv e) ∙ r
          step₄ = ↓-app=cst-out step₃

  conj : {i : I} (w : W P i) (ω : w == w)
    → (l-inv : (j : I) (l : Leaf P w j) → l == l [ (λ x → Leaf P x j) ↓ ω ])
    → (n-inv : (g : Ops P) (n : Node P w g) → n == n [ (λ x → Node P x g) ↓ ω ])
    → ω == idp
  conj (lf i) ω l-inv n-inv = {!!} -- This is actually trivial.
  conj (nd {i} (f , ϕ)) ω l-inv n-inv = {!!} 

    where yeah : idp == ap (λ x → i , x) (fst= (–> (W=-equiv P) ω)) ∙ idp
          yeah = lemma f f ϕ ϕ ω (_ , f) idp idp (n-inv (_ , f) (inl idp))


  -- So, like, is this stupid or can it be pushed further?
  -- What if you play with the global/local setup?  What if
  -- the map induces the identity on the *total* space of nodes.

  -- I know you've been here before, but, like, you have to find
  -- some kind of simple and compelling explanation for rigidity,
  -- whatever it is and if it exists....

  -- Okay, in the first step, we are going to think
  -- about just grafting.  To what extent is *it* rigid?

  GraftData : (i : I) → Type ℓ
  GraftData i = Σ (W P i) (λ w → Decor (Fr P) w (W P))

  -- I guess v doesn't actually appear here ...
  -- graft-eqvs : {i : I} (w : W P i) (ψ : ∀ j → Leaf P w j → W P j) → Type ℓ
  -- graft-eqvs {i} w ψ =
  --   Σ (W P i) (λ v →
  --   Σ ((j : I) → Σ I (λ k → Σ (Leaf P w k) (λ l → Leaf P (ψ k l) j)) ≃ Leaf P (graft P w ψ) j) (λ α →
  --   (g : Ops P) → Node P w g ⊔ Σ I (λ k → Σ (Leaf P w k) (λ l → Node P (ψ k l) g)) ≃ Node P (graft P w ψ) g))

  -- Right, so, uh, this is just a product.
  -- Things will probably be easier if you
  -- split everything down to avoid path arithmetic.
  
  graft-eqvs : {i : I} (w : W P i) (ψ : ∀ j → Leaf P w j → W P j) → Type ℓ
  graft-eqvs {i} w ψ =
    Σ ((j : I) → Σ I (λ k → Σ (Leaf P w k) (λ l → Leaf P (ψ k l) j)) ≃ Leaf P (graft P w ψ) j) (λ α →
    (g : Ops P) → Node P w g ⊔ Σ I (λ k → Σ (Leaf P w k) (λ l → Node P (ψ k l) g)) ≃ Node P (graft P w ψ) g)

  -- And I guess you can be even more specific. Just write
  -- out exactly what the pathover is going to give you.
  -- It will say that for every index and every pair of
  -- leaves connected over the automorphism, evaluating
  -- the leaf equivalence returns the same leaf in the
  -- graft.

  -- Any idea why this might be useful?
  
  graft-el : {i : I} (w : W P i) (ψ : ∀ j → Leaf P w j → W P j)
    →  graft-eqvs w ψ
  graft-el w ψ = graft-leaf-eqv P w ψ , graft-node-eqv P w ψ

  -- The idea is that in analogy with what happens for
  -- substitution an flattening, maybe similarly automorphisms
  -- of the data which preserve the leaf and node equivalences
  -- are trivial?

  graft-rigid : {i : I} (w : W P i) (ψ : ∀ j → Leaf P w j → W P j)
    → (aut : Path {A = GraftData i} (w , ψ) (w , ψ))
    → (po : graft-el w ψ == graft-el w ψ [ uncurry (graft-eqvs) ↓ aut ])
    → aut == idp
  graft-rigid (lf i) ψ aut po = {!↓-Π-out (↓-Σ-fst po)!}
  graft-rigid (nd x) ψ aut po = {!!}

  -- postulate

  --   Ψ₀ : CohWit M
  --   Ψ₁ : CohWit (SlcMgm Ψ₀)

  -- P₀ = P
  -- P₁ = P // M
  -- P₂ = (P // M) // SlcMgm Ψ₀

  -- -- So, my idea is to do this in complete generality.
  -- -- I think you will need the completely general statement
  -- -- Anyway, so why not try to write out what you think it
  -- -- should say and see what happens?

  -- rigidity : {i : I} {f : Op P i}
  --   → (w : W P i) (e : μ M w == f) 
  --   → (coh : W P₂ ((i , f) , (w , e)))
  --   → (α : μ (SlcMgm Ψ₁) coh == μ (SlcMgm Ψ₁) coh)
  --   → (j : I) (g : Op P j) (v : W P j) (r : μ M v == g) 
  --   → (n : Node P₁ (fst (μ (SlcMgm Ψ₁) coh)) (((j , g) , v , r)))
  --   → r == r
  -- rigidity w e coh α = {!fst (μ (SlcMgm Ψ₁) coh)!}

  -- -- Okay, there it is.  That's your claim.
  -- -- Moreover, there should be a map in the other direction
  -- -- as well which is essentially trivial (just ap the equality
  -- -- everywhere).  

  -- -- In fact, I expect that something like this should be an
  -- -- eqivalence.  However, in order to get the coherence you
  -- -- are looking for, I think it should suffice to show that
  -- -- it is a retraction.
  

  -- -- postulate

  -- --   Ψ : CohWit (Subst P) (subst-mgm P)

  -- -- SlcSubst : Poly (Ops (Subst P))
  -- -- SlcSubst = Subst P // subst-mgm P

  -- -- SlcMgm : PolyMagma SlcSubst
  -- -- SlcMgm = slc-mgm (Subst P) (subst-mgm P) Ψ

  -- -- -- Okay, so we suppose we have proven the associativity
  -- -- -- and so on for the slice which results in the coherence
  -- -- -- witness above by general principles.  Now I think we
  -- -- -- can state the main idea:

  -- -- rigidity : {i : I} {f : Op P i}
  -- --   → (w : W P i) (α : Frame P w f)
  -- --   → (coh : W SlcSubst ((i , f) , (w , α)))
  -- --   → (e : μ SlcMgm coh == μ SlcMgm coh)
  -- --   → e == idp
  -- -- rigidity {i} {f} w α (lf .((i , f) , w , α)) e = {!e!}

  -- --   where lem : idp == ap (λ z → flatn P z , flatn-frm P z) (fst= e)
  -- --         lem = anti-whisker-right (snd (μ SlcMgm (lf ((i , f) , w , α))))
  -- --                 (↓-app=cst-out (snd= e))
          
  -- -- rigidity {i} .(flatn P pd) .(flatn-frm P pd) (nd ((pd , idp) , θ)) e =
  -- --   {!↓-app=cst-out (snd= e)!}

  -- -- Okay.  So we see indeed that this is significantly different
  -- -- from what you were trying to prove before.

  -- -- So, the first thing we have to show is that any
  -- -- automorphism of this corolla:
  -- -- 
  -- -- nd ((w , α) , (λ j p → lf j)) , Ψ (lf ((i , f) , w , α))
  -- --
  -- -- which preserves the proof that multiplication in the
  -- -- slice is w must in fact be the identity.
  -- --

  -- -- So, what's quite fantastic about that is that this is
  -- -- something extremely concrete that you can check by hand.
  -- -- And it sounds extremely plausible!!

  -- -- And now in the second case, we have to prove that
  -- -- automorphisms of

  -- -- subst (Subst P) pd (λ g n →
  -- --    slc-flatn (Subst P) (subst-mgm P) (θ g n) ,
  -- --    slc-flatn-frm (Subst P) (subst-mgm P) (θ g n))
  -- --  , Ψ (nd ((pd , idp) , θ))

  -- -- preserving the laws are also trivial.

