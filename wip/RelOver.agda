{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import wip.PolyOver
open import wip.PolyEquiv

module wip.RelOver  where

  -- We can pull a relation back
  Rel↑ : ∀ {ℓ} {I : Type ℓ} {P : Poly I}
    → (Q : PolyOver P) (R : PolyRel P)
    → PolyRel (ΣPoly P Q)
  Rel↑ Q R ((i , j) , (f , g)) (w , α) =
    R (i , f) (W↓ Q w , Frame↓ Q α)

  --
  -- ... Alternatively, there is a natural choice of polynomial
  -- over the slice of P by the relation R.  These two
  -- constructions are compatible in the sense that:
  --
  --   (ΣPoly P Q // Rel↑ R) ≃ (ΣPoly (P // R) (Q ⇑ R))
  --
  _⇑_ : ∀ {ℓ} {I : Type ℓ} {P : Poly I}
    → (Q : PolyOver P) (R : PolyRel P)
    → PolyOver (P // R)
  Sort↓ (_⇑_ {P = P} Q R) (i , f) = Σ (Sort↓ Q i) (Op↓ Q f)
  Op↓ (_⇑_ {P = P} Q R) {i , f} ((w , α) , r) (j , g) =
    Σ (InFrame (ΣPoly P Q) ((i , j) , (f , g)))
      (λ { (v , β) → W↓ Q v , Frame↓ Q β == w , α })
  Param↓ (_⇑_ {P = P} Q R) ((._ , ._) , _) ((v , β) , idp) n =
    fst (<– (W↓-nd-eqv Q v _ _) n)

  module _ {ℓ} {I : Type ℓ} {P : Poly I} (Q : PolyOver P) (R : PolyRel P) where
  
    RelSort≃ : Ops (ΣPoly P Q) ≃ Σ (Ops P) (Sort↓ (Q ⇑ R))
    RelSort≃ = equiv to from to-from from-to

      where to : Ops (ΣPoly P Q) → Σ (Ops P) (Sort↓ (Q ⇑ R))
            to ((i , j) , (f , g)) = (i , f) , (j , g)

            from : Σ (Ops P) (Sort↓ (Q ⇑ R)) → Ops (ΣPoly P Q)
            from ((i , f) , (j , g)) = (i , j) , (f , g)

            to-from : (x : Σ (Ops P) (Sort↓ (Q ⇑ R))) → to (from x) == x
            to-from ((i , f) , (j  , g)) = idp

            from-to : (x : Ops (ΣPoly P Q)) → from (to x) == x
            from-to ((i , j) , (f , g)) = idp

    RelOp≃-to : (fg : Ops (ΣPoly P Q))
      → Op (ΣPoly P Q // Rel↑ Q R) fg
      → Op (ΣPoly (P // R) (Q ⇑ R)) (–> RelSort≃ fg)
    RelOp≃-to ((i , j) , (f , g)) ((w , α) , r) =
      ((W↓ Q w , Frame↓ Q α) , r) , ((w , α) , idp)

    RelOp≃-from : (fg : Ops (ΣPoly P Q))
      → Op (ΣPoly (P // R) (Q ⇑ R)) (–> RelSort≃ fg)
      → Op (ΣPoly P Q // Rel↑ Q R) fg
    RelOp≃-from ((i , j) , (f , g)) (((._ , ._) , r) , (w , α) , idp)
      = (w , α) , r

    RelOp≃-to-from : (fg : Ops (ΣPoly P Q))
      → (w : Op (ΣPoly (P // R) (Q ⇑ R)) (–> RelSort≃ fg))
      → RelOp≃-to fg (RelOp≃-from fg w) == w
    RelOp≃-to-from ((i , j) , (f , g)) (((._ , ._) , r) , (w , α) , idp) = idp

    RelOp≃-from-to : (fg : Ops (ΣPoly P Q))
      → (w : Op (ΣPoly P Q // Rel↑ Q R) fg)
      → RelOp≃-from fg (RelOp≃-to fg w) == w
    RelOp≃-from-to ((i , j) , (f , g)) ((w , α) , r) = idp

    RelOp≃ : (fg : Ops (ΣPoly P Q))
      → Op (ΣPoly P Q // Rel↑ Q R) fg
      ≃ Op (ΣPoly (P // R) (Q ⇑ R)) (–> RelSort≃ fg)
    RelOp≃ fg = equiv (RelOp≃-to fg) (RelOp≃-from fg)
      (RelOp≃-to-from fg) (RelOp≃-from-to fg)

    RelParam≃-to : {fg : Ops (ΣPoly P Q)}
      → (w : Op (ΣPoly P Q // Rel↑ Q R) fg)
      → (hk : Ops (ΣPoly P Q))
      → Param (ΣPoly P Q // Rel↑ Q R) w hk
      → Param (ΣPoly (P // R) (Q ⇑ R)) (RelOp≃-to fg w) (–> RelSort≃ hk)
    RelParam≃-to {(i , j) , (f , g)} ((w , α) , r) ((h , k) , (s , t)) n =
      W↓-nd-to Q w h s ((k , t) , n) , 
      fst= (<–-inv-l (W↓-nd-eqv Q w h s) ((k , t) , n))
      
    RelParam≃-from : {fg : Ops (ΣPoly P Q)}
      → (w : Op (ΣPoly P Q // Rel↑ Q R) fg)
      → (hk : Ops (ΣPoly P Q))
      → Param (ΣPoly (P // R) (Q ⇑ R)) (RelOp≃-to fg w) (–> RelSort≃ hk)
      → Param (ΣPoly P Q // Rel↑ Q R) w hk
    RelParam≃-from {(i , j) , f , g} ((w , α) , r) ((h , k) , s , t) (n , e) = 
      transport (λ x → Node (ΣPoly P Q) w ((h , fst x) , (s , snd x))) e 
                (snd (W↓-nd-from Q w h s n))
                   
    RelParam≃-to-from : {fg : Ops (ΣPoly P Q)}
      → (w : Op (ΣPoly P Q // Rel↑ Q R) fg)
      → (hk : Ops (ΣPoly P Q))
      → (p : Param (ΣPoly (P // R) (Q ⇑ R)) (RelOp≃-to fg w) (–> RelSort≃ hk))
      → RelParam≃-to w hk (RelParam≃-from w hk p) == p
    RelParam≃-to-from {(i , j) , f , g} ((w , α) , r) ((h , ._) , s , ._) (n , idp) =
      pair= (<–-inv-r (W↓-nd-eqv Q w h s) n) (↓-app=cst-in' lem)

      where lem = fst= (<–-inv-l (W↓-nd-eqv Q w h s) (W↓-nd-from Q w h s n))
                     =⟨ ap fst= (! (<–-inv-adj' (W↓-nd-eqv Q w h s) n)) ⟩
                  fst= (ap (<– (W↓-nd-eqv Q w h s)) (<–-inv-r (W↓-nd-eqv Q w h s) n))
                    =⟨ ap-fst (<– (W↓-nd-eqv Q w h s)) ⟩ 
                  ap (λ x → fst (<– (W↓-nd-eqv Q w h s) x)) (<–-inv-r (W↓-nd-eqv Q w h s) n) ∎

    RelParam≃-from-to : {fg : Ops (ΣPoly P Q)}
      → (w : Op (ΣPoly P Q // Rel↑ Q R) fg)
      → (hk : Ops (ΣPoly P Q))
      → (p : Param (ΣPoly P Q // Rel↑ Q R) w hk)
      → RelParam≃-from w hk (RelParam≃-to w hk p) == p
    RelParam≃-from-to {(i , j) , (f , g)} ((w , α) , r) ((h , k) , (s , t)) n =
      let F x = Node (ΣPoly P Q) w ((h , fst x) , (s , snd x))
          e = fst= (<–-inv-l (W↓-nd-eqv Q w h s) ((k , t) , n))
      in transport F e (snd (W↓-nd-from Q w h s (W↓-nd-to Q w h s ((k , t) , n))))
           =⟨ transp-fst= (<–-inv-l (W↓-nd-eqv Q w h s) ((k , t) , n)) ⟩ 
         n ∎

    RelParam≃ : {fg : Ops (ΣPoly P Q)}
      → (w : Op (ΣPoly P Q // Rel↑ Q R) fg)
      → (hk : Ops (ΣPoly P Q))
      → Param (ΣPoly P Q // Rel↑ Q R) w hk
      ≃ Param (ΣPoly (P // R) (Q ⇑ R)) (RelOp≃-to fg w) (–> RelSort≃ hk)
    RelParam≃ w hk = equiv (RelParam≃-to w hk) (RelParam≃-from w hk)
                           (RelParam≃-to-from w hk) (RelParam≃-from-to w hk)

    Rel≃ : (ΣPoly P Q // Rel↑ Q R) ≃ₚ (ΣPoly (P // R) (Q ⇑ R))
    Sort≃ Rel≃ = RelSort≃
    Op≃ Rel≃ = RelOp≃
    Param≃ Rel≃ = RelParam≃

    -- postulate

    --   Rel= : Path {A = PolyType}
    --               (Ops (ΣPoly P Q) , (ΣPoly P Q // Rel↑))
    --               (Σ (Ops P) (Sort↓ (Q ⇑ R)) , ΣPoly (P // R) (Q ⇑ R))


    -- postulate

    --   flatn-inv-to : {i : I} (f : Op P i) {j : Sort↓ Q i} (g : Op↓ Q f j)
    --       → (pd : W (ΣPoly P Q // (Rel↑ Q R)) ((i , j) , f , g))
    --       → Path {A = InFrame P (i , f)}
    --              (W↓ Q (flatn (Rel↑ Q R) pd) , Frame↓ Q (flatn-frm (Rel↑ Q R) pd))
    --              (flatn R (W↓ (RelOver Q R) (–> (W≃ (Rel≃ Q R) _) pd)) , flatn-frm R (W↓ (RelOver Q R) (–> (W≃ (Rel≃ Q R) _) pd)))

    --   flatn-inv-from : {i : I} (f : Op P i) {j : Sort↓ Q i} (g : Op↓ Q f j)
    --       → (pd : W (ΣPoly (P // R) (RelOver Q R)) ((i , f) , (j , g)))
    --       → Path {A = InFrame P (i , f)}
    --              (W↓ Q (flatn (Rel↑ Q R) (<– (W≃ (Rel≃ Q R) _) pd)) , Frame↓ Q (flatn-frm (Rel↑ Q R) (<– (W≃ (Rel≃ Q R) _) pd)))
    --              (flatn R (W↓ (RelOver Q R) pd) , flatn-frm R (W↓ (RelOver Q R) pd))


    -- -- And there is probably a coherence here as well: the fact that apping one
    -- -- to the inverse of the other and then composing gives back the other.
    -- -- So *this* finally feels like what you've been looking for all along in
    -- -- terms of the "equivalence" or "globular" structure of the face maps.

    -- -- Presumably this will play a role in the proof of the pathover below.

    -- -- Easy, peasy!
    -- SubInvar↑ : SubInvar R → SubInvar (Rel↑ Q R)
    -- SubInvar↑ Ψ {(i , j) , (f , g)} pd =
    --   transport! (R (i , f))
    --              (flatn-inv-to _ _ pd)
    --              (Ψ (W↓ (RelOver Q R) (–> (W≃ (Rel≃ Q R) _) pd)))

  --   postulate

  --     -------------------------------------------------------------
  --     -- Okay.  Here is the first point: the pullback of the magma
  --     -- relation for the slice magma structure on P // R is equal
  --     -- to the magma relation for the slice magma structure of ΣPoly P Q
  --     -- when the relation R is subdivision invariant.
  --     -------------------------------------------------------------

  --     SlcRel= : (Ψ₀ : SubInvar R)
  --       → ⟪ SlcMgm (SubInvar↑ Ψ₀) ⟫ == Rel↑ (RelOver Q R) ⟪ SlcMgm Ψ₀ ⟫ [ RelType ↓ Rel= Q R ]

  -- --
  -- -- The final proof goes as follows:
  -- --
  -- -- 1) we obtain a proof that the slice magma relation is
  -- --    subdivision invariant by transporting along the
  -- --    equality above
  -- -- 2) therefore, the subdivision invariance on both sides
  -- --    is connected by a path over
  -- -- 3) therefore, the magmas obtained by slicing these proofs
  -- --    are themselves connected by a path over
  -- -- 4) hence we have a coherence structure on one if and only
  -- --    if we have one on the other, and this is the coinductive step
  -- --
  
  -- {-# TERMINATING #-}
  -- CohStruct↑ : ∀ {ℓ} {I : Type ℓ} (P : Poly I) (Q : PolyOver P)
  --   → (M : PolyMagma P) (C : CohStruct M)
  --   → CohStruct (SlcMgm (SubInvar↑ Q ⟪ M ⟫ (Ψ C)))
  -- Ψ (CohStruct↑ P Q M C) =
  --   SubInvar-transp! (Rel= Q ⟪ M ⟫)
  --                    (SlcRel= Q ⟪ M ⟫ (Ψ C))
  --                    (SubInvar↑ (RelOver Q ⟪ M ⟫) ⟪ M ⇙ (Ψ C) ⟫ (Ψ (H C)))
  -- H (CohStruct↑ P Q M C) =
  --   CohStruct-transp! (Rel= Q ⟪ M ⟫)
  --                     (SlcRel= Q ⟪ M ⟫ (Ψ C))
  --                     (SubInvar-po! (Rel= Q ⟪ M ⟫)
  --                                   (SlcRel= Q ⟪ M ⟫ (Ψ C))
  --                                   (SubInvar↑ (RelOver Q ⟪ M ⟫) ⟪ M ⇙ (Ψ C) ⟫ (Ψ (H C))))
  --                     (CohStruct↑ (P // ⟪ M ⟫)
  --                                 (RelOver Q ⟪ M ⟫)
  --                                 (M ⇙ Ψ C)
  --                                 (H C))

