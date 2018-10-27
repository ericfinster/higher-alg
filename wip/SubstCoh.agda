{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Substitution

module SubstCoh {ℓ} {I : Type ℓ} {P : Poly I} (R : PolyRel P) where

  -- The flatten relation
  FlattenRel : PolyRel (P // R)
  FlattenRel {i , f} pd (w , α , r) β = Σ (R (flatten R pd) f (flatten-frm R pd))
    (λ s → Path {A = Σ (Op (P // R) (i , f)) (Frame (P // R) pd) }
      ((flatten R pd , flatten-frm R pd , s) , bd-frame R pd)
      ((w , α , r) , β))

  -- Substituting a trivial decoration
  -- gives back the tree
  substitute-unit : {i : I} (w : W P i)
    → substitute R w (λ ic n → lf ic) == w
  substitute-unit (lf i) = idp
  substitute-unit (nd (f , ϕ)) =
    ap (λ x → nd (f , x)) (λ= (λ j → λ= (λ p → substitute-unit (ϕ j p))))


  -- -- Substitution is compatible with *horizontal* grafting
  -- -- Hmmm.  Maybe the more general version is a better way to go here ...
  -- graft-subst : {i : I} (w : W P i)
  --   → (ψ : (j : I) → Leaf P w j → W P j)
  --   → (κ : (jg : Σ I (Op P)) → Node P w (snd jg) → W (P // R) jg)
  --   → graft P (substitute R w κ) (λ j l → ψ j (substitute-lf-to R w κ j l))
  --   == substitute R (graft P w ψ) (λ jg n → Coprod-elim (κ jg) (λ _ → lf jg) (graft-node-from P w ψ (snd jg) n))
  -- graft-subst (lf i) ψ κ = ! (substitute-unit (ψ i idp))
  -- graft-subst (nd (f , ϕ)) ψ κ =
  --   let pd = κ (_ , f) (inl idp)
  --       p j l = flatten-frm-to R pd j l
  --       ε j l = substitute R (ϕ j (p j l)) (λ ic n → κ ic (inr (j , p j l , n)))
  --   in -- graft P (substitute R (nd (f , ϕ)) κ) (λ j l → ψ j (substitute-lf-to R (nd (f , ϕ)) κ j l))
  --      graft P (graft P (flatten R pd) ε) (λ j l → ψ j (substitute-lf-to R (nd (f , ϕ)) κ j l)) =⟨ {!(graft P (nd (f , ϕ)) ψ)!} ⟩
  --      graft P (flatten R pd) {!!} =⟨ idp ⟩ 
  --      substitute R (nd (f , (λ j p → graft P (ϕ j p) (λ k l → ψ k (j , p , l))))) (λ jg n → Coprod-elim (κ jg) (λ _ → lf jg) (graft-node-from P (nd (f , ϕ)) ψ (snd jg) n)) ∎
  --      -- substitute R (graft P (nd (f , ϕ)) ψ) (λ jg n → Coprod-elim (κ jg) (λ _ → lf jg) (graft-node-from P (nd (f , ϕ)) ψ (snd jg) n)) ∎

  -- -- Okay, yeah, so the first step is associativity of grafting.

  -- -- Substitution is compatible with *vertical* grafting
  -- subst-graft : {i : I} (w : W P i)
  --   → (κ : (j : Σ I (Op P)) → Node P w (snd j) → W (P // R) j)
  --   → (θ : (j : Σ I (Op P)) → Σ (Σ I (Op P)) (λ k → Σ (Node P w (snd k)) (λ p → Leaf (P // R) (κ k p) j)) →  W (P // R) j)
  --   → substitute R w (λ j p → graft (P // R) (κ j p) (λ k l → θ k (j , p , l)))
  --     == substitute R (substitute R w κ) (λ jg n → θ jg (substitute-nd-from R w κ jg n))
  -- subst-graft (lf i) κ θ = idp
  -- subst-graft (nd (f , ϕ)) κ θ = {!!}

  -- -- substitute (nd {i} (f , ϕ)) κ = 
  -- --   let pd = κ (i , f) (inl idp)
  -- --       p j l = flatten-frm-to pd j l
  -- --       ε j l = substitute (ϕ j (p j l)) (λ ic n → κ ic (inr (j , p j l , n)))
  -- --   in graft P (flatten pd) ε 



  -- -- What am I being asked to show here?
  -- -- I feel like I'm going in circles.  These relations seem
  -- -- true, but rather arbitrary.  How do I find a technique to
  -- -- understand what I am trying to say.


  --   -- -- The previous lemma is compatible with grafting ...
  --   -- subst-graft-lemma : {i : I} (w : W P i)
  --   --   → (ε : ∀ j → Leaf P w j → W P j)
  --   --   → graft P (substitute (Rl D) w (λ ic _ → lf ic))
  --   --           (λ j l → substitute (Rl D) (ε j (substitute-lf-to (Rl D) w (λ ic _ → lf ic) j l)) (λ ic _ → lf ic))
  --   --     == graft P w ε
  --   -- subst-graft-lemma (lf i) ε = subst-lemma (ε i idp)
  --   -- subst-graft-lemma (nd (c , δ)) ε = ap (λ d → nd (c , d)) (λ= (λ j → λ= (λ p → subst-graft-lemma (δ j p) (λ k l → ε k (j , p , l))))) 


  -- -- Here is a coherence which seems to be appropriate for
  -- -- use in the next guy....
  -- flatten-graft : {i : I} {f : Op P i}
  --   → (pd : W (P // R) (i , f))
  --   → (ψ : (j : Σ I (Op P)) → Leaf (P // R) pd j → W (P // R) j)
  --   → flatten R (graft (P // R) pd ψ)
  --     == substitute R (flatten R pd) (λ jg n → ψ jg (<– (bd-frame R pd jg) n))
  -- flatten-graft (lf .(_ , _)) κ = ! (graft-unit (flatten R (κ _ idp)))
  -- flatten-graft (nd ((lf i , α , r) , κ)) θ = idp
  -- flatten-graft (nd ((nd (f , ϕ) , α , r) , κ)) θ = {!flatten-graft (κ (_ , f) (inl idp)) (λ k l → θ k ((_ , f) , inl idp , l))!}


  -- -- Umm, okay, what about a graft subsitutue relation?  What would this look like?
  -- -- Oh.  Yes, there should certainly be a relation like this.  In the horizontal
  -- -- direction.  What does it say?

  -- -- It says that if you have a tree and a graft of it.  And for each of the
  -- -- local tree and grafted guys you have a higher substitution tree, then
  -- -- you can either substitute and recursively graft, or else graft first
  -- -- and then substitute using the induced decoration.

  -- -- Combined with what you have above, this is saying that substitution is
  -- -- compatible with grafting both *vertically* and *horizontally*.

  -- -- Yeah, and this guy seems to be asking that substitution
  -- -- be monadic in a sense.

  -- -- And this is actually interesting.  Because it's as if you're being asked to
  -- -- show that substitution satisfies the monadic laws in exactly the way you
  -- -- stated them for the set monad case.

  -- -- The thing is, it's clear that I'm generating a bunch of coherences, but in
  -- -- order to be systematic, I would really like to have some way of orgranizing
  -- -- them.  And I don't quite see that yet.

  -- -- And note that you've been looking for things that are sort of independent
  -- -- of the relation.  Well, I think this is one.
  
  -- normal : PolyRel (P // R) → Type ℓ
  -- normal F = {f : Ops P} (pd : W (P // R) f) (w : Op (P // R) f) (β : Frame (P // R) pd w)
  --   (r : F pd w β) → flatten R pd , flatten-frm R pd == fst w , fst (snd w) 

  --   -- Yeah, so like, if our relation RR doesn't imply at least that
  --   -- flatten R pd == w, then I don't see how to finish this.
  --   flatten-flatten : (RR : Relator (P // R)) (is-normal : normal RR)
  --     → {i : I} {f : Op P i}
  --     → (w : W P i) (α : Frame P w f) (r : R w f α)
  --     → (γ : W ((P // R) // RR) ((i , f) , (w , α , r)))
  --     → flatten R (flatten RR γ) == w
  --   flatten-flatten RR is-n w α r (lf ._) = substitute-unit w
  --   flatten-flatten RR is-n w α r (nd ((pd , β , rr) , κ)) =
  --     flatten-subst RR is-n pd κ ∙ is-n pd (w , α , r) β rr


  --     flatten-subst :  {f : Ops P} (pd : W (P // fst C) f)
  --       → (κ : (g : Σ (Ops P) (Op (P // fst C))) → Node (P // fst C) pd g → W ((P // fst C) // fst D) g)
  --       → flatten C (substitute D pd κ) == flatten C pd
        
  -- mutual

  --   -- Okay, and this path-over looks like just an extra coherence
  --   -- of flatten-flatten.
  --   flatten-subst : (RR : Relator (P // R)) (is-normal : normal RR)
  --     → {i : I} {f : Op P i} (pd : W (P // R) (i , f))
  --     → (κ : (j : Σ (Σ I (Op P)) (Op (P // R))) → Node (P // R) pd (snd j) → W ((P // R) // RR) j)
  --     → flatten R (substitute RR pd κ) == flatten R pd 
  --   flatten-subst RR is-n (lf .(_ , _)) κ = idp
  --   flatten-subst RR is-n (nd ((w , α , r) , ψ)) κ =
  --     flatten-graft (flatten RR (κ (_ , w , α , r) (inl idp))) ψ' ∙
  --     ap (uncurry (substitute R)) (pair= (flatten-flatten RR is-n w α r (κ (_ , w , α , r) (inl idp))) {!!}) 

  --     where w' : W (P // R) _
  --           w' = flatten RR (κ (_ , w , α , r) (inl idp))

  --           ψ' : (j : Σ I (Op P)) → Leaf (P // R) w' j → W (P // R) j
  --           ψ' j l = substitute RR (ψ j (flatten-frm-to RR (κ (_ , w , α , r) (inl idp)) j l))
  --                      (λ ic n → κ ic (inr (j , flatten-frm-to RR (κ (_ , w , α , r) (inl idp)) j l , n)))

  --   -- Yeah, so like, if our relation RR doesn't imply at least that
  --   -- flatten R pd == w, then I don't see how to finish this.
  --   flatten-flatten : (RR : Relator (P // R)) (is-normal : normal RR)
  --     → {i : I} {f : Op P i}
  --     → (w : W P i) (α : Frame P w f) (r : R w f α)
  --     → (γ : W ((P // R) // RR) ((i , f) , (w , α , r)))
  --     → flatten R (flatten RR γ) == w
  --   flatten-flatten RR is-n w α r (lf ._) = substitute-unit w
  --   flatten-flatten RR is-n w α r (nd ((pd , β , rr) , κ)) =
  --     flatten-subst RR is-n pd κ ∙ is-n pd (w , α , r) β rr

  -- -- So think about it.  What could the relationship be?
  -- -- It has to do with flattening a vertical graft in the
  -- -- filling polynomial....

  -- -- So. If I have a graft in the filling polynomial and I compute its
  -- -- flattening, what do I get?  Ahhh, I think I see.  Well, I should
  -- -- get an induced decoration on the flattened tree of the base guy.
  -- -- And flattening the whole tree should be the same as substituting
  -- -- into the flattened guy this induced decoration.  See what I mean?

  -- -- Yup.  This sounds right.


  -- postulate

  --   substitute-unit-frm : {i : I} (w : W P i)
  --     → (g : Op P i) (α : Frame P w g) (r : R w g α)
  --     → flatten-frm R (corolla (P // R) (w , α , r)) == α [ (λ w' → Frame P w' g) ↓ substitute-unit w ]

  --   -- Since the previous coherence needs nothing about the relator, I would
  --   -- conjecture that this one doesn't either.  Let me go ahead and write it
  --   -- that way, and we'll have to analyze this later.
  --   -- flatten-subst : (RR : Relator (P // R))
  --   --   → {i : I} {f : Op P i} (pd : W (P // R) (i , f))
  --   --   → (θ : (j : Σ (Σ I (Op P)) (Op (P // R))) → Node (P // R) pd (snd j) → W ((P // R) // RR) j)
  --   --   → flatten R (substitute RR pd θ) == flatten R pd 


  -- -- Okay, and I think you should rewrite this section to use the
  -- -- magma relator of a polynomial magma.  This is the one which
  -- -- will be most applicable to the set monad case.
  -- CR : Relator (P // R)
  -- CR {i , f} pd (w , α , r) β = 
  --   Σ (R (flatten R pd) f (flatten-frm R pd)) (λ s → 
  --     Path {A = Σ (Op (P // R) (i , f)) (Frame (P // R) pd)}
  --       ((flatten R pd , flatten-frm R pd , s) , bd-frame R pd)
  --       ((w , α , r) , β))
        
  -- -- Exactly.  And this looks perfectly plausible.
  -- globularity : {i : I} (f : Op P i)
  --   → (w : W P i) (α : Frame P w f) (r : R w f α)
  --   → (γ : W ((P // R) // CR) ((i , f) , (w , α , r)))
  --   → flatten R (flatten CR γ) == w
  -- globularity f w α r (lf ._) = substitute-unit w
  -- globularity f ._ ._ r (nd ((pd , ._ , .r , idp) , θ)) =
  --   flatten-subst CR (λ pd wt β rr → fst= (fst= (snd rr))) pd θ

  -- --
  -- --  Some notes about proving the susbtitute-unit-frm coherence.
  -- --

  -- -- Okay, I'm going to try to describe the relationhip that I think
  -- -- I am being asked for: given a leaf of substitute w and
  -- -- a leaf of w, if they are related by a path over the unit map,
  -- -- then applying the substitute leaf map to one gives the other.

  -- -- substitute-lf-to : {i : I} (w : W P i)
  -- --   → (κ : (c : Σ I (Op P)) → Node P w (snd c) → W (P // R) c)
  -- --   → (j : I) → Leaf P (substitute w κ) j → Leaf P w j

  -- -- substitute-unit-lf-to : {i : I} (w : W P i)
  -- --   → (j : I) (l₀ : Leaf P (substitute R w (λ ic n → lf ic)) j) (l₁ : Leaf P w j)
  -- --   → l₀ == l₁ [ (λ x → Leaf P x j) ↓ substitute-unit w ]
  -- --   → substitute-lf-to R w (λ ic n → lf ic) j l₀ == l₁
  -- -- substitute-unit-lf-to (lf i) .i idp idp idp = idp
  -- -- substitute-unit-lf-to (nd (f , ϕ)) j (i₀ , p₀ , l₀) (i₁ , p₁ , l₁) q =
  -- --   {!!}

  -- -- Okay, exactly.  And I think this will finish things off down below.
  -- -- Just have to massage everything into the correct form.

  -- -- Yeah, I still don't get it.  There doesn't seem to be an induction
  -- -- hypothesis, since we don't expect a frame from a fixed branch to g.
  -- -- So wtf?
  -- -- substitute-unit-frm-aux : {i : I} (w : W P i)
  -- --   → (g : Op P i) (α : Frame P w g) (r : R w g α)
  -- --   → ∀ j 
  -- --   → (l₀ : Leaf P (substitute R w (λ ic n → lf ic)) j)
  -- --   → (l₁ : Leaf P w j)
  -- --   → (q : l₀ == l₁ [ (λ x → Leaf P x j) ↓ substitute-unit w ])
  -- --   → flatten-frm-to R (corolla (P // R) (w , α , r)) j l₀ == –> (α j) l₁ 
  -- -- substitute-unit-frm-aux (lf i) g α r .i idp .idp idp = idp
  -- -- substitute-unit-frm-aux (nd (f , ϕ)) g α r j (i₀ , p₀ , l₀) (i₁ , p₁ , l₁) q =
  -- --   ap (fst (α j)) (pair= i₀==i₁ (↓-Σ-in {!!} {!↓-Σ-snd (↓-Σ-snd po)!}))

  -- --   where po : (i₀ , p₀ , l₀) == (i₁ , p₁ , l₁) [ (λ x → Leaf P (nd (f , x)) j) ↓  (λ= (λ j₁ → λ= (λ p → substitute-unit (ϕ j₁ p)))) ]
  -- --         po = ↓-ap-out (λ x → Leaf P x j) (λ x → nd (f , x)) (λ= (λ j₁ → λ= (λ p → substitute-unit (ϕ j₁ p)))) q

  -- --         i₀==i₁ : i₀ == i₁
  -- --         i₀==i₁ = ↓-cst-out (↓-Σ-fst po)

  -- --         p₀==p₁ : p₀ == p₁ [ (λ z → Param P f (snd z)) ↓ (pair= (λ= (λ j₁ → λ= (λ p → substitute-unit (ϕ j₁ p)))) (↓-Σ-fst po)) ]
  -- --         p₀==p₁ = ↓-Σ-fst (↓-Σ-snd po)

  -- -- So, uh, yeah, I think we need to use the induction hypothesis.
  -- -- But how exactly does one do this?

  -- -- Yeah, that's what I don't understand. For the induction hypothesis,
  -- -- I would need a frame from some branch of w to g.  But there's isn't
  -- -- such a thing in general.

  -- -- fst (α j) (i₀ , p₀ , substitute-lf-to (λ {;i₁} → R) (ϕ i₀ p₀) (λ ic n → lf ic) j l₀)
  -- -- fst (α k) (i₁ , p₁ , l₁)

  -- --flatten R pd == flatten R (substitute CR pd θ)

