{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import PolyMonad
open import wip.PolyEquiv
open import wip.PolyPaths

module wip.PolyOver where

  record PolyOver {ℓ} {I : Type ℓ} (P : Poly I) : Type (lsucc ℓ) where
    field
    
      Sort↓ : I → Type ℓ
      Op↓ : {i : I} (f : Op P i) (j : Sort↓ i) → Type ℓ
      Param↓ : {i : I} (f : Op P i) {j : Sort↓ i} (g : Op↓ f j)
        → {k : I} (p : Param P f k) → Sort↓ k 

  open PolyOver public

  ΣPoly : ∀ {ℓ} {I : Type ℓ} (P : Poly I) (Q : PolyOver P) → Poly (Σ I (Sort↓ Q))
  Op (ΣPoly P Q) (i , j) = Σ (Op P i) (λ f → Op↓ Q f j) 
  Param (ΣPoly P Q) (f , g) (k , l) = Σ (Param P f k) (λ p → Param↓ Q f g p == l)

  module _ {ℓ} {I : Type ℓ} {P : Poly I} (Q : PolyOver P) where

    -- Parameters are equivalent
    Param↓-eqv : {i : I} (f : Op P i) {j : Sort↓ Q i} (g : Op↓ Q f j)
      → (k : I) → Param P f k ≃ Σ (Sort↓ Q k) (λ h → Param (ΣPoly P Q) (f , g) (k , h))
    Param↓-eqv f g k = equiv (λ p → Param↓ Q f g p , p , idp)
                             (λ { (._ ,  p , idp) → p })
                             (λ { (._ , p , idp) → idp })
                             (λ p → idp)

    -- The induced map on trees from a morphism of polynomials.
    W↓ : {i : I} {j : Sort↓ Q i} → W (ΣPoly P Q) (i , j) → W P i
    W↓ (lf (i , j)) = lf i
    W↓ (nd {i , j} ((f , g) , ϕ)) =
      nd (f , λ k p → W↓ (ϕ (k , Param↓ Q f g p) (p , idp)))

    -- Leaves in a projected tree
    W↓-lf-to : {i : I} {j : Sort↓ Q i} (w : W (ΣPoly P Q) (i , j)) (k : I)
      → Σ (Sort↓ Q k) (λ m → Leaf (ΣPoly P Q) w (k , m))
      → Leaf P (W↓ w) k 
    W↓-lf-to (lf (i , j)) i (j , idp) = idp
    W↓-lf-to (nd ((f , g) , ϕ)) k (m , ((n , ._) , (p , idp) , l)) =
      n , p , W↓-lf-to (ϕ (n , Param↓ Q f g p) (p , idp)) k (m , l)

    W↓-lf-from : {i : I} {j : Sort↓ Q i} (w : W (ΣPoly P Q) (i , j)) (k : I)
      → Leaf P (W↓ w) k
      → Σ (Sort↓ Q k) (λ l → Leaf (ΣPoly P Q) w (k , l))
    W↓-lf-from (lf (i , j)) .i idp = j , idp
    W↓-lf-from (nd ((f , g) , ϕ)) k (m , p , l) = 
      let (n , l') = W↓-lf-from (ϕ (m , Param↓ Q f g p) (p , idp)) k l
      in n , (m , Param↓ Q f g p) , (p , idp) , l'

    W↓-lf-to-from : {i : I} {j : Sort↓ Q i} (w : W (ΣPoly P Q) (i , j)) (k : I)
      → (l : Leaf P (W↓ w) k)
      → W↓-lf-to w k (W↓-lf-from w k l) == l
    W↓-lf-to-from (lf (i , j)) .i idp = idp
    W↓-lf-to-from (nd ((f , g) , ϕ)) k (m , p , l) =
      ap (λ x → (m , p , x)) (W↓-lf-to-from (ϕ (m , Param↓ Q f g p) (p , idp)) k l)

    W↓-lf-from-to : {i : I} {j : Sort↓ Q i} (w : W (ΣPoly P Q) (i , j)) (k : I)
      → (l : Σ (Sort↓ Q k) (λ m → Leaf (ΣPoly P Q) w (k , m)))
      → W↓-lf-from w k (W↓-lf-to w k l) == l
    W↓-lf-from-to (lf .(i , j)) i (j , idp) = idp
    W↓-lf-from-to (nd ((f , g) , ϕ)) k (m , ((n , ._) , (p , idp) , l)) =
      ap (λ x → (fst x , (n , Param↓ Q f g p) , (p , idp) , snd x))
        (W↓-lf-from-to (ϕ (n , Param↓ Q f g p) (p , idp)) k (m , l))

    W↓-lf-eqv : {i : I} {j : Sort↓ Q i} (w : W (ΣPoly P Q) (i , j)) (k : I)
      → Σ (Sort↓ Q k) (λ l → Leaf (ΣPoly P Q) w (k , l)) ≃ Leaf P (W↓ w) k
    W↓-lf-eqv w k = equiv (W↓-lf-to w k) (W↓-lf-from w k)
                          (W↓-lf-to-from w k) (W↓-lf-from-to w k)

    -- Nodes in a projected tree
    W↓-nd-to : {i : I} {j : Sort↓ Q i} (w : W (ΣPoly P Q) (i , j)) (k : I) (h : Op P k)
      → Σ (Sort↓ Q k) (λ m → Σ (Op↓ Q h m) (λ o → Node (ΣPoly P Q) w ((k , m) , (h , o))))
      → Node P (W↓ w) (k , h)
    W↓-nd-to (lf .(_ , _)) k h (m , g , lift ())
    W↓-nd-to (nd ((f , g) , ϕ)) k .f (m , .g , inl idp) = inl idp
    W↓-nd-to (nd ((f , g) , ϕ)) k h (m , l , inr ((k₀ , ._) , (p , idp) , n)) =
      inr (k₀ , p , W↓-nd-to (ϕ (k₀ , Param↓ Q f g p) (p , idp)) k h (m , l , n))

    W↓-nd-from : {i : I} {j : Sort↓ Q i} (w : W (ΣPoly P Q) (i , j)) (k : I) (h : Op P k)
      → Node P (W↓ w) (k , h)
      → Σ (Sort↓ Q k) (λ m → Σ (Op↓ Q h m) (λ o → Node (ΣPoly P Q) w ((k , m) , (h , o))))
    W↓-nd-from (lf .(_ , _)) k h (lift ())
    W↓-nd-from (nd ((f , g) , ϕ)) k .f (inl idp) = _ , g , inl idp
    W↓-nd-from (nd ((f , g) , ϕ)) k h (inr (k₀ , p , n)) =
      let (m , t , n') = W↓-nd-from (ϕ (k₀ , Param↓ Q f g p) (p , idp)) k h n
      in m , t , inr ((k₀ , Param↓ Q f g p) , (p , idp) , n')

    W↓-nd-to-from : {i : I} {j : Sort↓ Q i} (w : W (ΣPoly P Q) (i , j)) (k : I) (h : Op P k)
      → (n : Node P (W↓ w) (k , h))
      → W↓-nd-to w k h (W↓-nd-from w k h n) == n
    W↓-nd-to-from (lf .(_ , _)) k h (lift ())
    W↓-nd-to-from (nd ((f , g) , ϕ)) k .f (inl idp) =  idp
    W↓-nd-to-from (nd ((f , g) , ϕ)) k h (inr (k₀ , p , n)) =
      ap (λ x → inr (k₀ , p , x)) (W↓-nd-to-from (ϕ (k₀ , Param↓ Q f g p) (p , idp)) k h n)

    W↓-nd-from-to : {i : I} {j : Sort↓ Q i} (w : W (ΣPoly P Q) (i , j)) (k : I) (h : Op P k)
      → (n : Σ (Sort↓ Q k) (λ m → Σ (Op↓ Q h m) (λ o → Node (ΣPoly P Q) w ((k , m) , (h , o)))))
      → W↓-nd-from w k h (W↓-nd-to w k h n) == n
    W↓-nd-from-to (lf .(_ , _)) k h (m , g , lift ())
    W↓-nd-from-to (nd ((f , g) , ϕ)) k .f (m , .g , inl idp) = idp
    W↓-nd-from-to (nd ((f , g) , ϕ)) k h (m , l , inr ((k₀ , ._) , (p , idp) , n)) =
      ap (λ x → fst x , fst (snd x) , inr ((k₀ , Param↓ Q f g p) , (p , idp) , snd (snd x)))
         (W↓-nd-from-to (ϕ (k₀ , Param↓ Q f g p) (p , idp)) k h (m , l , n))

    W↓-nd-eqv : {i : I} {j : Sort↓ Q i} (w : W (ΣPoly P Q) (i , j)) (k : I) (h : Op P k)
      → Σ (Sort↓ Q k) (λ m → Σ (Op↓ Q h m) (λ o → Node (ΣPoly P Q) w ((k , m) , (h , o))))
      ≃ Node P (W↓ w) (k , h)
    W↓-nd-eqv w k h = equiv (W↓-nd-to w k h) (W↓-nd-from w k h)
                            (W↓-nd-to-from w k h) (W↓-nd-from-to w k h)

  --   -- Projection of frames  (probably has to be unfolded...)
  --   Frame↓ : {i : I} {f : Op P i} {j : Sort↓ Q i} {g : Op↓ Q f j} {w : W (ΣPoly P Q) (i , j)}
  --     → Frame (ΣPoly P Q) w (f , g)
  --     → Frame P (W↓ w) f
  --   Frame↓ {f = f} {g = g} {w = w} α k =
  --     (W↓-lf-eqv w k ∘e
  --      Σ-emap-r (λ h → α (k , h) ⁻¹) ∘e
  --      Param↓-eqv f g k) ⁻¹
       
  --     -- (Param↓-eqv f g k) ⁻¹ ∘e {!!} ∘e (W↓-lf-eqv w k)⁻¹
      
  --     -- equiv to from to-from from-to

  --     -- where to : Leaf P (W↓ w) k → Param P f k
  --     --       to l = let (h , l') = W↓-lf-from w k l
  --     --              in fst (–> (α (k , h)) l')

  --     --       from : Param P f k → Leaf P (W↓ w) k
  --     --       from p = W↓-lf-to w k (Param↓ Q f g p , <– (α (k , Param↓ Q f g p)) (p , idp))

  --     --       to-from : (p : Param P f k) → to (from p) == p
  --     --       to-from p = {!!}

  --     --       from-to : (l : Leaf P (W↓ w) k) → from (to l) == l
  --     --       from-to l = {!!}


  --   module _  (R : PolyRel P) where

  --     -- A relation on P pulls back to a relation
  --     -- on the total polynomial ....
      
  --     Rel↑ : PolyRel (ΣPoly P Q)
  --     Rel↑ ((i , j) , (f , g)) (w , α) =
  --       R (i , f) (W↓ w , Frame↓ α)

  --     --
  --     -- ... Alternatively, there is a natural choice of polynomial
  --     -- over the slice of P by the relation R.  These two
  --     -- constructions are compatible in the sense that:
  --     --
  --     --   (ΣPoly P Q // Rel↑ R) ≃ (ΣPoly (P // R) (RelOver P R Q))
  --     --

  --     RelOver : PolyOver (P // R)
  --     Sort↓ RelOver (i , f) = Σ (Sort↓ Q i) (Op↓ Q f)
  --     Op↓ RelOver {i , f} ((w , α) , r) (j , g) =
  --       Σ (W (ΣPoly P Q) (i , j)) (λ v →
  --       Σ (Frame (ΣPoly P Q) v (f , g)) (λ β →
  --       W↓ v , Frame↓ β == w , α))
  --     Param↓ RelOver ((._ , ._) , r) (v , _ , idp) {k , h} n = 
  --       let (s , o , _) = <– (W↓-nd-eqv v k h) n
  --       in s , o

  --     RelSort≃ : Ops (ΣPoly P Q) ≃ Σ (Ops P) (Sort↓ RelOver)
  --     RelSort≃ = equiv to from to-from from-to

  --       where to : Ops (ΣPoly P Q) → Σ (Ops P) (Sort↓ RelOver)
  --             to ((i , j) , (f , g)) = (i , f) , (j , g)

  --             from : Σ (Ops P) (Sort↓ RelOver) → Ops (ΣPoly P Q)
  --             from ((i , f) , (j , g)) = (i , j) , (f , g)

  --             to-from : (x : Σ (Ops P) (Sort↓ RelOver)) → to (from x) == x
  --             to-from ((i , f) , (j  , g)) = idp

  --             from-to : (x : Ops (ΣPoly P Q)) → from (to x) == x
  --             from-to ((i , j) , (f , g)) = idp

  --     RelOp≃-to : (fg : Ops (ΣPoly P Q))
  --       → Op (ΣPoly P Q // Rel↑) fg
  --       → Op (ΣPoly (P // R) RelOver) (–> RelSort≃ fg)
  --     RelOp≃-to ((i , j) , (f , g)) ((w , α) , r) =
  --       ((W↓ w , Frame↓ α) , r) , (w , α , idp)

  --     RelOp≃-from : (fg : Ops (ΣPoly P Q))
  --       → Op (ΣPoly (P // R) RelOver) (–> RelSort≃ fg)
  --       → Op (ΣPoly P Q // Rel↑) fg
  --     RelOp≃-from ((i , j) , (f , g)) (((._ , ._) , r) , w , α , idp)
  --       = (w , α) , r

  --     RelOp≃-to-from : (fg : Ops (ΣPoly P Q))
  --       → (w : Op (ΣPoly (P // R) RelOver) (–> RelSort≃ fg))
  --       → RelOp≃-to fg (RelOp≃-from fg w) == w
  --     RelOp≃-to-from ((i , j) , (f , g)) (((._ , ._) , r) , w , α , idp) = idp

  --     RelOp≃-from-to : (fg : Ops (ΣPoly P Q))
  --       → (w : Op (ΣPoly P Q // Rel↑) fg)
  --       → RelOp≃-from fg (RelOp≃-to fg w) == w
  --     RelOp≃-from-to ((i , j) , (f , g)) ((w , α) , r) = idp

  --     RelOp≃ : (fg : Ops (ΣPoly P Q))
  --       → Op (ΣPoly P Q // Rel↑) fg
  --       ≃ Op (ΣPoly (P // R) RelOver) (–> RelSort≃ fg)
  --     RelOp≃ fg = equiv (RelOp≃-to fg) (RelOp≃-from fg)
  --       (RelOp≃-to-from fg) (RelOp≃-from-to fg)

  --     Rel≃ : (ΣPoly P Q // Rel↑) ≃ₚ (ΣPoly (P // R) RelOver)
  --     Sort≃ Rel≃ = RelSort≃
  --     Op≃ Rel≃ = RelOp≃
  --     Param≃ Rel≃ = {!!}

  --     postulate

  --       Rel= : Path {A = PolyType}
  --                   (Ops (ΣPoly P Q) , (ΣPoly P Q // Rel↑))
  --                   (Σ (Ops P) (Sort↓ RelOver) , ΣPoly (P // R) RelOver)


  -- module _ {ℓ} {I : Type ℓ} {P : Poly I} (Q : PolyOver P) (R : PolyRel P) where

  --   -- And this is somehow the main idea: flattening commutes with the
  --   -- equivalence defined above (in both directions ...)
    
  --   postulate

  --     flatn-inv-to : {i : I} (f : Op P i) {j : Sort↓ Q i} (g : Op↓ Q f j)
  --         → (pd : W (ΣPoly P Q // (Rel↑ Q R)) ((i , j) , f , g))
  --         → Path {A = InFrame P (i , f)}
  --                (W↓ Q (flatn (Rel↑ Q R) pd) , Frame↓ Q (flatn-frm (Rel↑ Q R) pd))
  --                (flatn R (W↓ (RelOver Q R) (–> (W≃ (Rel≃ Q R) _) pd)) , flatn-frm R (W↓ (RelOver Q R) (–> (W≃ (Rel≃ Q R) _) pd)))

  --     flatn-inv-from : {i : I} (f : Op P i) {j : Sort↓ Q i} (g : Op↓ Q f j)
  --         → (pd : W (ΣPoly (P // R) (RelOver Q R)) ((i , f) , (j , g)))
  --         → Path {A = InFrame P (i , f)}
  --                (W↓ Q (flatn (Rel↑ Q R) (<– (W≃ (Rel≃ Q R) _) pd)) , Frame↓ Q (flatn-frm (Rel↑ Q R) (<– (W≃ (Rel≃ Q R) _) pd)))
  --                (flatn R (W↓ (RelOver Q R) pd) , flatn-frm R (W↓ (RelOver Q R) pd))


  --   -- And there is probably a coherence here as well: the fact that apping one
  --   -- to the inverse of the other and then composing gives back the other.
  --   -- So *this* finally feels like what you've been looking for all along in
  --   -- terms of the "equivalence" or "globular" structure of the face maps.

  --   -- Presumably this will play a role in the proof of the pathover below.

  --   -- Easy, peasy!
  --   SubInvar↑ : SubInvar R → SubInvar (Rel↑ Q R)
  --   SubInvar↑ Ψ {(i , j) , (f , g)} pd =
  --     transport! (R (i , f))
  --                (flatn-inv-to _ _ pd)
  --                (Ψ (W↓ (RelOver Q R) (–> (W≃ (Rel≃ Q R) _) pd)))

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

