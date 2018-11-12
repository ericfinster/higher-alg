{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Substitution
open import PolyMonad

-- Realizing opetopes
module wip.Opetopes {ℓ} {I : Type ℓ} {P : Poly I} (M : PolyMagma P) (C : CohStruct M) where

  open CohStruct 
  
  Opetope : ℕ → Type ℓ
  
  OpPoly : (n : ℕ) → Poly (Opetope n)
  OpMagma : (n : ℕ) → PolyMagma (OpPoly n)
  OpCoh : (n : ℕ) → CohStruct (OpMagma n)

  Opetope O = I
  Opetope (S n) = Ops (OpPoly n)

  OpPoly O = P
  OpPoly (S n) = OpPoly n // MgmRel (OpMagma n) 

  OpMagma O = M
  OpMagma (S n) = SlcMgm (Ψ (OpCoh n))

  OpCoh O = C
  OpCoh (S n) = H (OpCoh n)
  
  ∂𝕆 : (n : ℕ) → Opetope n → Type ℓ
  𝕎 : (n : ℕ) {i : Opetope n} → W (OpPoly n) i → Type ℓ
  ∂⁻ : (n : ℕ) {i : Opetope n} (f : Op (OpPoly n) i) → Type ℓ

  𝕆 : (n : ℕ) → Opetope n → Type ℓ
  𝕆 n i = ⊤ * ∂𝕆 n i
  
  in-∂⁻-Op : (n : ℕ) {i : Opetope n} (f : Op (OpPoly n) i)
    → (j : Opetope n) (p : Param (OpPoly n) f j)
    → 𝕆 n j → ∂⁻ n f
  in-∂⁻-Op n f j p x = {!!}

  in-∂⁺-W : (n : ℕ) {i : Opetope n} (w : W (OpPoly n) i)
    → 𝕆 n i → 𝕎 n w

  in-∂⁻ : (n : ℕ) {i : Opetope n} (f : Op (OpPoly n) i)
    → ∂𝕆 n i → ∂⁻ n f
  in-∂⁻ = {!!}

  ∂⁻ O f = Arity P f
  ∂⁻ (S n) ((w , α) , r) = 𝕎 n w

  ∂𝕆 O i = Lift ⊥
  ∂𝕆 (S n) (i , f) = Pushout (span (𝕆 n i) (∂⁻ n f) (∂𝕆 n i) jright (in-∂⁻ n f))

  𝕎 n (lf i) = 𝕆 n i
  𝕎 n (nd {i} (f , ϕ)) = 
    let ispace = Σ (Opetope n) (λ j → Σ (Param (OpPoly n) f j) (λ p → 𝕆 n j))
        wspace = Σ (Opetope n) (λ j → Σ (Param (OpPoly n) f j) (λ p → 𝕎 n (ϕ j p)))
        ospace = ⊤ * Pushout (span (𝕆 n i) (∂⁻ n f) (∂𝕆 n i) jright (in-∂⁻ n f))
    in Pushout (span ospace wspace ispace 
      (λ { (j , p , x) → jright (right (in-∂⁻-Op n f j p x)) })
      (λ { (j , p , x) → j , p , in-∂⁺-W n (ϕ j p) x }))

  in-∂⁺-W n (lf i) x = x
  in-∂⁺-W n (nd (f , ϕ)) x = left (right (left x))

  -- Right, simple idea is that there is an inclusion map
  -- which, for every parameter maps the opetope of that
  -- shape into the source bounday

  -- Yeah, having a kind of generic pasting of trees seems like
  -- it would be super useful.  So I think you should base the
  -- construction around the assumption that this is the fundamental
  -- idea: trees are constructed by gluing the base opetopes of
  -- branches to their image in the source of an operation.

  -- ∂𝕆 : (n : ℕ) → Opetope n → Type ℓ
  -- ∂𝕆 O i = Lift ⊥
  -- ∂𝕆 (S n) (i , f) = Pushout (span (∂⁺ (S n) (i , f)) (∂⁻ (S n) (i , f)) (∂𝕆 n i) {!!} {!!})

  -- Right, this is the pushout of the realization of the
  -- frame (i.e. the target realization) and the source of
  -- our given operation along a given inclusion.

--   ∂⁺-Op : (n : ℕ) {i : Opetope n} → Op (OpPoly n) i → Type ℓ
--   ∂⁻-Op : (n : ℕ) {i : Opetope n} → Op (OpPoly n) i → Type ℓ
--   ∂-Op : (n : ℕ) {i : Opetope n} → Op (OpPoly n) i → Type ℓ
--   ●-Op : (n : ℕ) {i : Opetope n} → Op (OpPoly n) i → Type ℓ
--   in-∂-Op : (n : ℕ) {i : Opetope n} (f : Op (OpPoly n) i) → ∂-Op n f → ●-Op n f

--   ∂⁺-W : (n : ℕ) {i : Opetope n} → W (OpPoly n) i → Type ℓ
--   ∂⁻-W : (n : ℕ) {i : Opetope n} → W (OpPoly n) i → Type ℓ
--   ∂-W : (n : ℕ) {i : Opetope n} → W (OpPoly n) i → Type ℓ
--   ●-W : (n : ℕ) {i : Opetope n} → W (OpPoly n) i → Type ℓ
--   in-∂-W : (n : ℕ) {i : Opetope n} (w : W (OpPoly n) i) → ∂-W n w → ●-W n w

--   -- Compatibilities
  
--   ∂-equiv : (n : ℕ) {o : Opetope n} (w : W (OpPoly n) o)
--     → ∂-W n w ≃ ∂-Op n (μ (OpMagma n) w) 

--   -- Realization of operations
  
--   ∂⁺-Op O f = Lift ⊤
--   ∂⁺-Op (S n) {i , f} w = ●-Op n f

--   ∂⁻-Op O f = Arity P f
--   ∂⁻-Op (S n) {i , f} ((w , α) , r) = ●-W n w

--   ∂-Op O f = ⊤ ⊔ Arity P f
--   ∂-Op (S n) {i , ._} ((w , ._) , idp) =
--     let f = μ (OpMagma n) w
--     in Pushout (span (●-Op n f) (●-W n w) (∂-W n w)
--                      (in-∂-Op n f ∘ –> (∂-equiv n w))
--                      (in-∂-W n w))

--   ●-Op n f = ⊤ * (∂-Op n f)
--   in-∂-Op n f = jright

--   -- Realizations of trees
  
--   ∂⁺-W n w = {!!}
--   ∂⁻-W n w = {!!}

--   ∂-W O w = ⊤ ⊔ Σ I (Leaf P w)
--   ∂-W (S n) {i , f} pd with μ (OpMagma (S n)) pd
--   ∂-W (S n) {i , ._} pd | ((w , ._) , idp) = 
--     let f = μ (OpMagma n) w
--     in Pushout (span (●-Op n f) (●-W n w) (∂-W n w)
--                      (in-∂-Op n f ∘ –> (∂-equiv n w))
--                      (in-∂-W n w))
    
--   -- Yes, so far so good.  And now what?

--   ●-W n (lf i) = {!!}
--   ●-W n (nd (f , ϕ)) = {!!}
--     -- let ispace = Σ (Opetope n) (λ j → Σ (Param (OpPoly n) f j) (λ p → 𝕆 n j))
--     -- in {!!}

--   -- The idea for a tree is that there should be should be, like
--   -- an "interface space" which is the sum over the parameters of
--   -- f of a copy of the incoming boundary of the tree attached to
--   -- that parameter.

--   -- But will this actually work generically?
--   -- Ah, so we need to know that there is a map from this "interface space"
--   -- to the incoming source of f itself.

--   -- Like, can this work generically?  Indeed, there's something kind
--   -- of fishy about the way things repeat here.

--   -- Yeah, and so, like, there should be a map from this parameter space
--   -- to the union (Σ) of all the trees as well as to the incoming source
--   -- of f.  The result should then be the pushout along this map.

--   in-∂-W = {!!}
  
--   -- Equivalences

--   ∂-equiv n w = {!!}

-- --   ∂Op : (n : ℕ) {o : Opetope n} (p : Op (OpPoly n) o) → Type ℓ
-- --   ●Op : (n : ℕ) {o : Opetope n} (p : Op (OpPoly n) o) → Type ℓ
-- --   in-∂Op : (n : ℕ) {o : Opetope n} (p : Op (OpPoly n) o) → ∂Op n p → ●Op n p

-- --   ∂W : (n : ℕ) {o : Opetope n} (w : W (OpPoly n) o) → Type ℓ
-- --   ●W : (n : ℕ) {o : Opetope n} (w : W (OpPoly n) o) → Type ℓ
-- --   in-∂W : (n : ℕ) {o : Opetope n} (w : W (OpPoly n) o) → ∂W n w → ●W n w

-- --   -- Given a pasting diagram, its boundary and that of its
-- --   -- multiplication are equivalent.
-- --   ∂-equiv : (n : ℕ) {o : Opetope n} (w : W (OpPoly n) o)
-- --     → ∂W n w ≃ ∂Op n (μ (OpMagma n) w) 

-- --   ∂Op O f = ⊤ ⊔ Arity P f
-- --   ∂Op (S n) {i , ._} ((w , ._) , idp) =
-- --     let p = μ (OpMagma n) w
-- --     in Pushout (span (●Op n p) (●W n w) (∂Op n p)
-- --                      (in-∂Op n p)
-- --                      ((in-∂W n w) ∘ <– (∂-equiv n w)))

-- --   ●Op n p = ⊤ * (∂Op n p) 
-- --   in-∂Op n p = jright

-- --   -- Now, what is the ∂ of a successor tree?
-- --   ∂W O w = ⊤ ⊔ Σ I (Leaf P w)
-- --   ∂W (S n) {o , p} w = {!!}
-- -- --     Pushout (span (●Op n p) (●W n canopy) (∂Op n p)
-- -- --                   (in-∂Op n p)
-- -- --                   (in-∂W n (canopy) ∘ –> (∂-equiv n p canopy canopy-frm (umm n p w)))) 

-- -- --     where canopy : W (OpPoly n) o
-- -- --           canopy = flatten (ΣR (OpRel n) (Ref (OpType n))) w

-- -- --           canopy-frm : Frame (OpPoly n) canopy p
-- -- --           canopy-frm = flatten-frm (ΣR (OpRel n) (Ref (OpType n))) w

-- --   ●W O (lf i) = Lift ⊤
-- --   ●W O (nd (f , ϕ)) = ⊤ * (Σ (Arity P f) (λ a → ●W O (ϕ (fst a) (snd a))))
-- --   ●W (S n) w = {!!}

-- --   in-∂W = {!!}
  
-- -- --   -- Excellent!!
-- -- --   in-∂W O (lf i) (inl tt) = lift tt
-- -- --   in-∂W O (lf i) (inr (.i , idp)) = lift tt
-- -- --   in-∂W O (nd (f , ϕ)) (inl tt) = jleft tt
-- -- --   in-∂W O (nd (f , ϕ)) (inr (j , k , p , l)) =
-- -- --     jright ((k , p) , (in-∂W O (ϕ k p) (inr (j , l))))
-- -- --   in-∂W (S n) w = {!!}

-- --   ∂-equiv O w = ⊔-emap (ide ⊤) (Σ-emap-r (μ-frm M w))
-- --   ∂-equiv (S n) w = {!!}

-- -- --   -- And here's where I think we will have to work...
-- -- --   ∂-equiv O p w α r = ⊔-emap (ide ⊤) (Σ-emap-r (λ j → (α j)⁻¹))
-- -- --   ∂-equiv (S n) ._ w ._ ((r , s) , idp) =
-- -- --     Pushout-emap ((span-map (idf _) (idf _) (idf _)
-- -- --       (comm-sqr (λ x → idp))
-- -- --       (comm-sqr (λ x → {!!}))) ,
-- -- --       (idf-is-equiv _ , idf-is-equiv _ , idf-is-equiv _))

-- -- --   -- So then it looks like we just have to show that the
-- -- --   -- equivalence obtained here doesn't depend on the element
-- -- --   -- chosen.  But is that true?

-- -- --   -- The realization of an opetope is always just the filled
-- -- --   -- version of itself viewed as an operation as above...
-- -- --   𝕆 : {n : ℕ} → Opetope n → Type ℓ
-- -- --   𝕆 {O} i = Lift ⊤
-- -- --   𝕆 {S n} (o , p) = ●Op n p


-- -- --   -- Hmmm. Completely crazy.  Because it looks like if we assume that
-- -- --   -- the refinement is trivial, then we can complete this.  But then
-- -- --   -- that starts to look very much like the multiplicative structure
-- -- --   -- on the universe, no?
-- -- --   umm : (n : ℕ) {o : Opetope n} (p : Op (OpPoly n) o)
-- -- --     → (w : W (OpPoly (S n)) (o , p))
-- -- --     → OpRel n (flatten (ΣR (OpRel n) (Ref (OpType n))) w) p
-- -- --               (flatten-frm (ΣR (OpRel n) (Ref (OpType n))) w)
-- -- --   umm O p w = lift tt
-- -- --   umm (S n) {τ , σ} (w , α , (r , s)) coh = (umm n σ (flatten R₁ coh) , t) ,
-- -- --     globularity (OpRel n) (Ref (OpType n)) (Ref (Hom (OpType n))) w α (r , s)
-- -- --       coh (umm n σ (flatten R₁ coh) , t) {!!}

-- -- --     where R₀ = (ΣR (OpRel n) (Ref (OpType n)))
-- -- --           R₁ = (ΣR (FlattenRel R₀) (Ref (Hom (OpType n))))

-- -- --           t : Ref (OpType n) (flatten R₀ (flatten R₁ coh)) σ
-- -- --                 (flatten-frm R₀ (flatten R₁ coh)) (umm n σ (flatten R₁ coh))
-- -- --           t = {!!}

-- -- --   -- Yeah, so, like.  It's similar to below where I need ummm n to be
-- -- --   -- equal to any other guy.  But can't you prove this by induction?

-- -- --   -- I think you have to try.  Because that base case looks pretty fucking
-- -- --   -- trivial.  And if this were in fact true, I feel like it's really
-- -- --   -- close to the coherent structure on the universe.

-- -- --   -- Ummm.  But wait, do I even need it to be contractible?
-- -- --   -- because, like, I already have the globular equalities,
-- -- --   -- so the element can be just obtained by transport from r, no?

-- -- --   -- Hold on, hold on.  Doesn't this show ... it's like.  You've
-- -- --   -- constructed this magma.  And then you need to show, to have
-- -- --   -- the universe, that every composite is give by this one.
-- -- --   -- On the other hand, I feel like the witnesses in the next
-- -- --   -- level are exactly the statement that it *is* this one.

-- -- --   -- So there's something funny going on here.  In any case, I
-- -- --   -- didn't expect something so interesting to pop out of this.
-- -- --   -- But it seems something kinda cool is happening.

