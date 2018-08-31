{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial

module SetMonad where

  record PolyMagma {ℓ} {I : Type ℓ} (P : Poly I) : Type ℓ where
    field

      mult : {i : I} (w : W P i) → Op P i
      mult-frm : {i : I} (w : W P i) → Frame P w (mult w)

  open PolyMagma
  
  module _ {ℓ} {I : Type ℓ} (P : Poly I) where

    Fr : Poly I
    Op Fr = W P
    Param Fr w = Leaf P w

    fr-mult : {i : I} (u : W Fr i) → W P i
    fr-mult (lf i) = lf i
    fr-mult (nd (w , ψ)) = graft P w (λ j l → fr-mult (ψ j l))

    fr-frm : {i : I} (u : W Fr i) → Frame Fr u (fr-mult u)
    fr-frm (lf i) j = ide (i == j)
    fr-frm (nd (w , ψ)) j = (graft-leaf-eqv P w (λ j l → fr-mult (ψ j l)) j)⁻¹ ∘e
      (Σ-emap-r (λ k → Σ-emap-r (λ l → fr-frm (ψ k l) j)))

    fr-magma : PolyMagma Fr
    mult fr-magma = fr-mult
    mult-frm fr-magma = fr-frm

    ind-mult : (M : PolyMagma P) → {i : I} (u : W Fr i) → W P i
    ind-mult M (lf i) = lf i
    ind-mult M (nd (w , ψ)) = nd (mult M w , λ j p → ind-mult M (ψ j (<– (mult-frm M w j) p)))

    -- Usual normalization problems expected, but at least this gives the right answer ...
    ind-mult-frm : (M : PolyMagma P) → {i : I} (u : W Fr i) → Frame Fr u (ind-mult M u)
    ind-mult-frm M (lf i) j = ide _
    ind-mult-frm M (nd (w , ψ)) j = Σ-emap-r (λ k → Σ-emap-r (λ p → ind-mult-frm M (ψ k (<– (mult-frm M w k) p)) j) ∘e
      (Σ-emap-l (λ p → Leaf Fr (ψ k p) j) ((mult-frm M w k)⁻¹))⁻¹)

      -- where A : Type ℓ
      --       A = Σ I (λ k → Σ (Leaf P w k) (λ p → Leaf Fr (ψ k p) j))

      --       B : Type ℓ
      --       B = Σ I (λ k → Σ (Param P (mult M w) k) (λ p → Leaf P (ind-mult M (ψ k (<– (mult-frm M w k) p))) j))

      --       to : A → B
      --       to (k , l₀ , l₁) = k , –> (mult-frm M w k) l₀ ,
      --         transport (λ x → Leaf P x j)
      --                   (ap (λ x → ind-mult M (ψ k x))
      --                   (! (<–-inv-l (mult-frm M w k) l₀))) (–> (ind-mult-frm M (ψ k l₀) j) l₁) 

      --       from : B → A
      --       from (k , p , l) = k , <– (mult-frm M w k) p , <– (ind-mult-frm M (ψ k (<– (mult-frm M w k) p)) j) l


  record SetMonad {ℓ} {I : Type ℓ} (P : Poly I) : Type ℓ where
    field

      sort-is-groupoid : has-level 1 I
      op-is-groupoid : (i : I) → has-level 1 (Op P i)
      param-is-groupoid : {i : I} (f : Op P i) (j : I) → has-level 1 (Param P f j)

      mag : PolyMagma P
      
      assoc : {i : I} (u : W (Fr P) i) → mult mag (fr-mult P u) == mult mag (ind-mult P mag u)

      -- We just ask that the values agree, but this is enough that the
      -- frames are actually equal.
      assoc-frm : {i : I} (u : W (Fr P) i) (j : I) (l : Leaf (Fr P) u j)
        → fst (mult-frm mag (fr-mult P u) j) (fst (fr-frm P u j) l)
        == fst (mult-frm mag (ind-mult P mag u) j) (fst (ind-mult-frm P mag u j) l)
           [ (λ f → Param P f j) ↓ assoc u ]


  open SetMonad

  -- Phew.  Saved your ass here!!!
  weird : ∀ {ℓ} {I : Type ℓ} (P : Poly I) (M : PolyMagma P)
    → (p-is-set : {i : I} (f : Op P i) (j : I) → is-set (Param P f j))
    → {i : I} (w : W P i) (j : I) → is-set (Leaf P w j)
  weird P M p-is-set w j = equiv-preserves-level ((mult-frm M w j)⁻¹) ⦃ p-is-set (mult M w) j  ⦄

  module _ {ℓ} {I : Type ℓ} (P : Poly I) (M : SetMonad P) where


    -- Idea is clear: from a set monad, pass to the canonical fillers given
    -- by the identity types and show that this is again a set monad.

    MndRel : Relator P
    MndRel w f α = (f , α) == mult (mag M) w , mult-frm (mag M) w

    -- Exactly.  And now the idea is to construct a multiplication
    -- on this guy.  I believe it should be the case that the laws
    -- you have to prove are in fact living in types which are propositions.
    -- (constructors and leaves?)  Hmmm.  Actually, the leaves need not
    -- be (and won't be in general) a set.  *But* the frames are maps
    -- between the leaves and the parameters, which are a set.  So by
    -- choosing the equivalence correctly, we should be okay.

    HomPoly : Poly (Σ I (Op P))
    HomPoly = P // MndRel
    
    -- Oh crap.  But the parameters of the hom polynomial are the
    -- nodes of the given tree.  And these are *not* a set in general
    -- because they have the truncation level of the type of sorts,
    -- which we expect to be a groupoid.

    -- Hmmm.  Not sure how I will get around this....

    -- Crazy.  As you show above, if you have a magma, then this automatically
    -- reduces the truncation level of the leaves.  So, constructing the equivalence
    -- between nodes of your "multiplied" tree and the canopy of the coherence
    -- will actually *imply* that the nodes of the derived guy are a set.

    -- In other words, you must first construct the multiplication and
    -- so on, and the last ingredient will be the fact that the parameters
    -- are in fact a set.

    -- Wow, that almost gave me a heart attack.

    hom-sort-is-groupoid : has-level 1 (Σ I (Op P))
    hom-sort-is-groupoid = Σ-level (sort-is-groupoid M) (op-is-groupoid M)

    -- Right, so this shows that, indeed, that the values of MndRel are
    -- sets.  Not sure if this helps, but there you go.
    hom-op-is-groupoid : {i : I} (f : Op P i) → has-level 1 (Op HomPoly (i , f))
    hom-op-is-groupoid {i} f = Σ-level (W-level P (op-is-groupoid M) i) (λ w →
      Σ-level (Frame-level P (sort-is-groupoid M) (param-is-groupoid M) w f) (λ f →
        =-preserves-level (Σ-level (op-is-groupoid M i)
          (Frame-level P (sort-is-groupoid M) (param-is-groupoid M) w))))

    hom-param-is-groupoid : {i : I} (f : Op P i) (h : Op HomPoly (i , f))
      → {j : I} (g : Op P j)
      → has-level 1 (Param HomPoly h (j , g))
    hom-param-is-groupoid f (w , α , r) = Node-level P (sort-is-groupoid M)
      (op-is-groupoid M) (param-is-groupoid M) w 
  
    -- So there you have it.  We have stability of the truncation level
    -- for groupoids, but not sets.  That is really bad news.

    -- But this is strange.  Are you missing something?
    -- Because suppose that this thing is indeed a monad.
    -- Then, frames should be equivalent to paths in the space
    -- of constructors, which is even *better* than a set.

    -- No. In the lowest dimension, it should be somehow rare that
    -- there is a *unique* frame, as is the case for the universe.

    -- But something is strange because, if you have a monad,
    -- then for every tree, the set of leaves is actually a *set*.


    -- Right, so does this fix the problem?


    hom-mult : {i : I} (f : Op P i) → W HomPoly (i , f) → Op HomPoly (i , f)
    hom-mult f (lf .(_ , f)) = corolla P f , corolla-lf-eqv P f , pair= {!!} {!!}
    hom-mult ._ (nd ((w , ._ , idp) , θ)) = {!!} , {!!} , {!!}

    -- Yeah, so here, the idea is to recursively flatten the node decoration
    -- of w to end up with, essentially, an element of the free monad, and then
    -- to multiply it.

    HomMult : PolyMagma HomPoly
    mult HomMult {i , f} = hom-mult f
    mult-frm HomMult = {!!}

    -- Yikes.  So this is seriously problematic, no?
