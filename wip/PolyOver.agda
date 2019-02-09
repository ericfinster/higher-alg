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

    -- The induced map on trees from a morphism of polynomials.
    W↓ : {i : I} {j : Sort↓ Q i} → W (ΣPoly P Q) (i , j) → W P i
    W↓ (lf (i , j)) = lf i
    W↓ (nd {i , j} ((f , g) , ϕ)) =
      nd (f , λ k p → W↓ (ϕ (k , Param↓ Q f g p) (p , idp)))

    W↓-lf-eqv-to : {i : I} {j : Sort↓ Q i} (w : W (ΣPoly P Q) (i , j)) (k : I)
      → Σ (Sort↓ Q k) (λ m → Leaf (ΣPoly P Q) w (k , m))
      → Leaf P (W↓ w) k 
    W↓-lf-eqv-to (lf (i , j)) i (j , idp) = idp
    W↓-lf-eqv-to (nd ((f , g) , ϕ)) k (m , ((n , ._) , (p , idp) , l)) =
      n , p , W↓-lf-eqv-to (ϕ (n , Param↓ Q f g p) (p , idp)) k (m , l)

    W↓-lf-eqv-from : {i : I} {j : Sort↓ Q i} (w : W (ΣPoly P Q) (i , j)) (k : I)
      → Leaf P (W↓ w) k
      → Σ (Sort↓ Q k) (λ l → Leaf (ΣPoly P Q) w (k , l))
    W↓-lf-eqv-from (lf (i , j)) .i idp = j , idp
    W↓-lf-eqv-from (nd ((f , g) , ϕ)) k (m , p , l) = 
      let (n , l') = W↓-lf-eqv-from (ϕ (m , Param↓ Q f g p) (p , idp)) k l
      in n , (m , Param↓ Q f g p) , (p , idp) , l'

    postulate
    
      W↓-lf-eqv : {i : I} {j : Sort↓ Q i} (w : W (ΣPoly P Q) (i , j)) (k : I)
        → Σ (Sort↓ Q k) (λ l → Leaf (ΣPoly P Q) w (k , l)) ≃ Leaf P (W↓ w) k

      W↓-nd-eqv : {i : I} {j : Sort↓ Q i} (w : W (ΣPoly P Q) (i , j)) (k : I) (h : Op P k)
        → Σ (Sort↓ Q k) (λ m → Σ (Op↓ Q h m) (λ o → Node (ΣPoly P Q) w ((k , m) , (h , o)))) ≃ Node P (W↓ w) (k , h)

      Frame↓ : {i : I} {f : Op P i} {j : Sort↓ Q i} {g : Op↓ Q f j} {w : W (ΣPoly P Q) (i , j)}
        → Frame (ΣPoly P Q) w (f , g)
        → Frame P (W↓ w) f
      -- Frame↓ f g w α k = {!!} ∘e (W↓-lf-eqv w k)⁻¹

    module _  (R : PolyRel P) where

      -- A relation on P pulls back to a relation
      -- on the total polynomial ....
      
      Rel↑ : PolyRel (ΣPoly P Q)
      Rel↑ ((i , j) , (f , g)) (w , α) =
        R (i , f) (W↓ w , Frame↓ α)

      --
      -- ... Alternatively, there is a natural choice of polynomial
      -- over the slice of P by the relation R.  These two
      -- constructions are compatible in the sense that:
      --
      --   (ΣPoly P Q // Rel↑ R) ≃ (ΣPoly (P // R) (RelOver P R Q))
      --

      RelOver : PolyOver (P // R)
      Sort↓ RelOver (i , f) = Σ (Sort↓ Q i) (Op↓ Q f)
      Op↓ RelOver {i , f} ((w , α) , r) (j , g) =
        Σ (W (ΣPoly P Q) (i , j)) (λ v →
        Σ (Frame (ΣPoly P Q) v (f , g)) (λ β →
        W↓ v , Frame↓ β == w , α))
      Param↓ RelOver ((._ , ._) , r) (v , _ , idp) {k , h} n = 
        let (s , o , _) = <– (W↓-nd-eqv v k h) n
        in s , o

      RelSort≃ : Ops (ΣPoly P Q) ≃ Σ (Ops P) (Sort↓ RelOver)
      RelSort≃ = equiv to from to-from from-to

        where to : Ops (ΣPoly P Q) → Σ (Ops P) (Sort↓ RelOver)
              to ((i , j) , (f , g)) = (i , f) , (j , g)

              from : Σ (Ops P) (Sort↓ RelOver) → Ops (ΣPoly P Q)
              from ((i , f) , (j , g)) = (i , j) , (f , g)

              to-from : (x : Σ (Ops P) (Sort↓ RelOver)) → to (from x) == x
              to-from ((i , f) , (j  , g)) = idp

              from-to : (x : Ops (ΣPoly P Q)) → from (to x) == x
              from-to ((i , j) , (f , g)) = idp

      RelOp≃-to : (fg : Ops (ΣPoly P Q))
        → Op (ΣPoly P Q // Rel↑) fg
        → Op (ΣPoly (P // R) RelOver) (–> RelSort≃ fg)
      RelOp≃-to ((i , j) , (f , g)) ((w , α) , r) =
        ((W↓ w , Frame↓ α) , r) , (w , α , idp)

      RelOp≃-from : (fg : Ops (ΣPoly P Q))
        → Op (ΣPoly (P // R) RelOver) (–> RelSort≃ fg)
        → Op (ΣPoly P Q // Rel↑) fg
      RelOp≃-from ((i , j) , (f , g)) (((._ , ._) , r) , w , α , idp)
        = (w , α) , r

      RelOp≃-to-from : (fg : Ops (ΣPoly P Q))
        → (w : Op (ΣPoly (P // R) RelOver) (–> RelSort≃ fg))
        → RelOp≃-to fg (RelOp≃-from fg w) == w
      RelOp≃-to-from ((i , j) , (f , g)) (((._ , ._) , r) , w , α , idp) = idp

      RelOp≃-from-to : (fg : Ops (ΣPoly P Q))
        → (w : Op (ΣPoly P Q // Rel↑) fg)
        → RelOp≃-from fg (RelOp≃-to fg w) == w
      RelOp≃-from-to ((i , j) , (f , g)) ((w , α) , r) = idp

      RelOp≃ : (fg : Ops (ΣPoly P Q))
        → Op (ΣPoly P Q // Rel↑) fg
        ≃ Op (ΣPoly (P // R) RelOver) (–> RelSort≃ fg)
      RelOp≃ fg = equiv (RelOp≃-to fg) (RelOp≃-from fg)
        (RelOp≃-to-from fg) (RelOp≃-from-to fg)

      Rel≃ : (ΣPoly P Q // Rel↑) ≃ₚ (ΣPoly (P // R) RelOver)
      Sort≃ Rel≃ = RelSort≃
      Op≃ Rel≃ = RelOp≃
      Param≃ Rel≃ = {!!}

      postulate

        Rel= : Path {A = PolyType}
                    (Ops (ΣPoly P Q) , (ΣPoly P Q // Rel↑))
                    (Σ (Ops P) (Sort↓ RelOver) , ΣPoly (P // R) RelOver)


  module _ {ℓ} {I : Type ℓ} {P : Poly I} (Q : PolyOver P) (R : PolyRel P) where

    -- And this is somehow the main idea: flattening commutes with the
    -- equivalence defined above (in both directions ...)
    
    postulate

      flatn-inv-to : {i : I} (f : Op P i) {j : Sort↓ Q i} (g : Op↓ Q f j)
          → (pd : W (ΣPoly P Q // (Rel↑ Q R)) ((i , j) , f , g))
          → Path {A = InFrame P (i , f)}
                 (W↓ Q (flatn (Rel↑ Q R) pd) , Frame↓ Q (flatn-frm (Rel↑ Q R) pd))
                 (flatn R (W↓ (RelOver Q R) (–> (W≃ (Rel≃ Q R) _) pd)) , flatn-frm R (W↓ (RelOver Q R) (–> (W≃ (Rel≃ Q R) _) pd)))

      flatn-inv-from : {i : I} (f : Op P i) {j : Sort↓ Q i} (g : Op↓ Q f j)
          → (pd : W (ΣPoly (P // R) (RelOver Q R)) ((i , f) , (j , g)))
          → Path {A = InFrame P (i , f)}
                 (W↓ Q (flatn (Rel↑ Q R) (<– (W≃ (Rel≃ Q R) _) pd)) , Frame↓ Q (flatn-frm (Rel↑ Q R) (<– (W≃ (Rel≃ Q R) _) pd)))
                 (flatn R (W↓ (RelOver Q R) pd) , flatn-frm R (W↓ (RelOver Q R) pd))


    -- And there is probably a coherence here as well: the fact that apping one
    -- to the inverse of the other and then composing gives back the other.
    -- So *this* finally feels like what you've been looking for all along in
    -- terms of the "equivalence" or "globular" structure of the face maps.

    -- Presumably this will play a role in the proof of the pathover below.

    -- Easy, peasy!
    SubInvar↑ : SubInvar R → SubInvar (Rel↑ Q R)
    SubInvar↑ Ψ {(i , j) , (f , g)} pd =
      transport! (R (i , f))
                 (flatn-inv-to _ _ pd)
                 (Ψ (W↓ (RelOver Q R) (–> (W≃ (Rel≃ Q R) _) pd)))

    postulate

      -------------------------------------------------------------
      -- Okay.  Here is the first point: the pullback of the magma
      -- relation for the slice magma structure on P // R is equal
      -- to the magma relation for the slice magma structure of ΣPoly P Q
      -- when the relation R is subdivision invariant.
      -------------------------------------------------------------

      SlcRel= : (Ψ₀ : SubInvar R)
        → ⟪ SlcMgm (SubInvar↑ Ψ₀) ⟫ == Rel↑ (RelOver Q R) ⟪ SlcMgm Ψ₀ ⟫ [ RelType ↓ Rel= Q R ]

  --
  -- The final proof goes as follows:
  --
  -- 1) we obtain a proof that the slice magma relation is
  --    subdivision invariant by transporting along the
  --    equality above
  -- 2) therefore, the subdivision invariance on both sides
  --    is connected by a path over
  -- 3) therefore, the magmas obtained by slicing these proofs
  --    are themselves connected by a path over
  -- 4) hence we have a coherence structure on one if and only
  --    if we have one on the other, and this is the coinductive step
  --
  
  {-# TERMINATING #-}
  CohStruct↑ : ∀ {ℓ} {I : Type ℓ} (P : Poly I) (Q : PolyOver P)
    → (M : PolyMagma P) (C : CohStruct M)
    → CohStruct (SlcMgm (SubInvar↑ Q ⟪ M ⟫ (Ψ C)))
  Ψ (CohStruct↑ P Q M C) =
    SubInvar-transp! (Rel= Q ⟪ M ⟫)
                     (SlcRel= Q ⟪ M ⟫ (Ψ C))
                     (SubInvar↑ (RelOver Q ⟪ M ⟫) ⟪ M ⇙ (Ψ C) ⟫ (Ψ (H C)))
  H (CohStruct↑ P Q M C) =
    CohStruct-transp! (Rel= Q ⟪ M ⟫)
                      (SlcRel= Q ⟪ M ⟫ (Ψ C))
                      (SubInvar-po! (Rel= Q ⟪ M ⟫)
                                    (SlcRel= Q ⟪ M ⟫ (Ψ C))
                                    (SubInvar↑ (RelOver Q ⟪ M ⟫) ⟪ M ⇙ (Ψ C) ⟫ (Ψ (H C))))
                      (CohStruct↑ (P // ⟪ M ⟫)
                                  (RelOver Q ⟪ M ⟫)
                                  (M ⇙ Ψ C)
                                  (H C))

