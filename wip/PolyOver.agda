{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import PolyMonad
open import wip.PolyEquiv

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


      Frame↓ : {i : I} (f : Op P i) {j : Sort↓ Q i} (g : Op↓ Q f j)
        → (w : W (ΣPoly P Q) (i , j)) 
        → Frame (ΣPoly P Q) w (f , g)
        → Frame P (W↓ w) f
      -- Frame↓ f g w α k = {!!} ∘e (W↓-lf-eqv w k)⁻¹

    -- Yeah, like, I'm starting to see.  This whole thing is just one
    -- long exercise in naturality.  You construct the isomorphism
    -- below.  Then you use it to define subdivision invariance as
    -- well as a magma on each side and so on.  These can all be
    -- regarded as path overs in various spaces of structures by
    -- univalence.

    -- I feel like the main theorem, then, is obtained by simply
    -- transporting all the various structures via the paths so
    -- obtained and that, therefore, the whole thing is natural
    -- because transporting the paths is.

    -- Your definitino of WΣ↓, for example, should simply consist
    -- of transporting the tree along the equivalence of polynomials
    -- and then applying W↓ on the other side.

    -- It feels like there should be a proof along these lines that
    -- does not need to wade into the details of how all the paths
    -- are constructed, but just usese the naturality provided by
    -- univalence to transport everything to the right place.

    module _  (R : PolyRel P) where

      -- From this information, we find that we can
      -- pull a relation back ....
      Rel↑ : PolyRel (ΣPoly P Q)
      Rel↑ ((i , j) , (f , g)) (w , α) =
        R (i , f) (W↓ w , Frame↓ f g w α)

      --
      -- ... or we can define a polynomial over the slice.
      -- These two constructions are compatible in that:
      --
      --   (ΣPoly P Q // Rel↑ R) ≃ (ΣPoly (P // R) (RelOver P R Q))
      --

      RelOver : PolyOver (P // R)
      Sort↓ RelOver (i , f) = Σ (Sort↓ Q i) (Op↓ Q f)
      Op↓ RelOver {i , f} ((w , α) , r) (j , g) =
        Σ (W (ΣPoly P Q) (i , j)) (λ v →
        Σ (Frame (ΣPoly P Q) v (f , g)) (λ β →
        W↓ v , Frame↓ f g v β == w , α))
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
              
      Rel≃ : (ΣPoly P Q // Rel↑) ≃ₚ (ΣPoly (P // R) RelOver)
      Sort≃ Rel≃ = RelSort≃
      Op≃ Rel≃ = {!!}
      Param≃ Rel≃ = {!!}


      -- Right.  So this is the claim.
      postulate

        RelPo : Path {A = Σ (Type ℓ) (Poly)}
          (Ops (ΣPoly P Q) , (ΣPoly P Q // Rel↑))
          (Σ (Ops P) (Sort↓ RelOver) , ΣPoly (P // R) RelOver)

      -- Hmmm. Maybe not. Maybe you do somehow need to
      -- explicitly spell it out....

      -- This should be induced by the equivalence below, but okay,
      -- I'll do it by hand here just to see what happens ...
      WΣ↓ : {i : I} (f : Op P i) {j : Sort↓ Q i} (g : Op↓ Q f j)
        → W (ΣPoly P Q // Rel↑) ((i , j) , f , g) → W (P // R) (i , f)
      WΣ↓ {i} f g (lf .((_ , _) , f , g)) = lf (i , f)
      WΣ↓ f g (nd (((w , α) , r) , κ)) = 
        let nr j n = <– (W↓-nd-eqv w (fst j) (snd j)) n
        in nd (((W↓ w , Frame↓ f g w α) , r) , (λ j n →
          WΣ↓ (snd j) (fst (snd (nr j n))) (κ _ (snd (snd (nr j n))))))

      -- Okay, and the central claim is that flattening is compatible
      -- with the above projection ...
      postulate

        lemma : {i : I} (f : Op P i) {j : Sort↓ Q i} (g : Op↓ Q f j)
          → (pd : W (ΣPoly P Q // Rel↑) ((i , j) , f , g))
          → Path {A = InFrame P (i , f)}
                 (flatn R (WΣ↓ f g pd) , flatn-frm R (WΣ↓ f g pd))
                 (W↓ (flatn Rel↑ pd) , Frame↓ f g (flatn Rel↑ pd) (flatn-frm Rel↑ pd))

      -- Easy, peasy!
      SubInvar↑ : SubInvar R → SubInvar Rel↑ 
      SubInvar↑ Ψ {(i , j) , (f , g)} pd = transport (λ x → R (i , f) x)
        (lemma f g pd) (Ψ (WΣ↓ f g pd))

  module _ {ℓ} {I : Type ℓ} {P : Poly I} (Q : PolyOver P) (R : PolyRel P) where

    -- Now, there should also be a definable
    -- magma on the sum.  Let's see about this
    Mgm↑ : SubInvar R → PolyMagma (ΣPoly (P // R) (RelOver Q R))
    μ (Mgm↑ Ψ) {(i , f) , (j , g)} pd = ((flatn R (W↓ (RelOver Q R) pd) , flatn-frm R (W↓ (RelOver Q R) pd)) ,
      Ψ (W↓ (RelOver Q R) pd)) , {!!} , {!!} , {!!}
    μ-frm (Mgm↑ Ψ) pd = {!bd-frm R (W↓ (RelOver Q R) pd)!}

    

    -- Right, but, like, shouldn't this just be defined
    -- as the transport of the slice magma over the equivalence?

    -- Okay, you don't care that there's a magma structure.
    -- What you care about is that lifting the slice invariance
    -- on the right is equal to the slice relation given by
    -- the slice magma structure on the lift of the first.

    -- Ahhh! Maddening!  I see how to proof goes, but it's a bit
    -- difficult to express!

    -- module _ (Mgm : PolyMagma P) (Coh : CohStruct Mgm)  where
    
      -- So, now, what happens next?
      -- The idea is that in this case, we still
      -- have a magma structure on the slice.

      -- Mgm↑ : PolyMagma (ΣPoly P Q // Rel↑ ⟪ Mgm ⟫)
      -- Mgm↑ = SlcMgm (SubInvar↑ ⟪ Mgm ⟫ (Ψ Coh))

      -- -- -- An invariant relation induces a magma on its slice
      -- -- SlcMgm : ∀ {ℓ} {I : Type ℓ} {P : Poly I} {R : PolyRel P}
      -- --   → SubInvar R → PolyMagma (P // R)
      -- -- μ (SlcMgm {R = R} Ψ) pd = (flatn R pd , flatn-frm R pd) , Ψ pd
      -- -- μ-frm (SlcMgm {R = R} Ψ) pd = bd-frm R pd

      -- Blorp : SubInvar ⟪ Mgm↑ ⟫
      -- Blorp {i , f} pd = need

      --   where need : (μ Mgm↑ (flatn ⟪ Mgm↑ ⟫ pd) , μ-frm Mgm↑ (flatn ⟪ Mgm↑ ⟫ pd)) == (f , flatn-frm ⟪ Mgm↑ ⟫ pd)
      --         need = {!Ψ (H Coh)!}

      --         tr : W ((ΣPoly P Q // Rel↑ ⟪ Mgm ⟫) // ⟪ Mgm↑ ⟫) (i , f)
      --         tr = pd

-- -- The relation induced by a magma
  -- ⟪_⟫ : ∀ {ℓ} {I : Type ℓ} {P : Poly I} (M : PolyMagma P) → PolyRel P
  -- ⟪_⟫ {P = P} M (i , f) (w , α) = Path {A = OutFrame P w}
  --   (μ M w , μ-frm M w) (f , α)

  -- CohStruct↑ : ∀ {ℓ} {I : Type ℓ} (P : Poly I) (Q : PolyOver P)
  --   → (M : PolyMagma P) (C : CohStruct M)
  --   → CohStruct (SlcMgm (SubInvar↑ Q ⟪ M ⟫ (Ψ C)))
  -- Ψ (CohStruct↑ P Q M C) {((i , j) , (f , g)) , ((w , α) , r)} pd = {!((i , j) , (f , g)) , ((w , α) , r)!}

  --   where Mgm↑ : PolyMagma (ΣPoly P Q // Rel↑ Q ⟪ M ⟫)
  --         Mgm↑ = SlcMgm (SubInvar↑ Q ⟪ M ⟫ (Ψ C))

  --         -- Right.  Another approach would be to define this magma
  --         -- on the other side and show that it is equivalent to the
  --         -- slice magma over the isomorphism of polynomials.
  --         Mgm↑' : PolyMagma (ΣPoly (P // ⟪ M ⟫) (RelOver Q ⟪ M ⟫))
  --         Mgm↑' = {!!}

  --         pd' : W ((ΣPoly P Q // Rel↑ Q ⟪ M ⟫) // ⟪ Mgm↑ ⟫) (((i , j) , (f , g)) , ((w , α) , r))
  --         pd' = pd

  --         -- Right.  This should be the image of pd under some kind of functorial
  --         -- action.  So, like, the idea is to apply subdivision invariance over on this
  --         -- side of the equivalence between the two polynomials and then transform it
  --         -- back.
  --         pd'' : W (ΣPoly (P // ⟪ M ⟫) (RelOver Q ⟪ M ⟫) // Rel↑ (RelOver Q ⟪ M ⟫) ⟪ M ⇙ Ψ C ⟫)
  --           (((i , f) , j , g) , ((W↓ Q w , Frame↓ Q f g w α) , r) , w , α , idp)
  --         pd'' = {!!}

  --         si : SubInvar ⟪ SlcMgm (Ψ C) ⟫
  --         si = Ψ (H C)

  --         test : SubInvar (Rel↑ (RelOver Q ⟪ M ⟫) ⟪ M ⇙ Ψ C ⟫)
  --         test = SubInvar↑ (RelOver Q ⟪ M ⟫) ⟪ M ⇙ (Ψ C) ⟫ (Ψ (H C))

  --     -- -- Easy, peasy!
  --     -- SubInvar↑ : SubInvar R → SubInvar Rel↑ 
  --     -- SubInvar↑ Ψ {(i , j) , (f , g)} pd = transport (λ x → R (i , f) x)
  --     --   (lemma f g pd) (Ψ (WΣ↓ f g pd))


  -- H (CohStruct↑ P Q M C) = {!!}

  --   -- where coind : CohStruct (SlcMgm (SubInvar↑ (RelOver Q ⟪ M ⟫) ⟪ M ⇙ (Ψ C) ⟫ (Ψ (H C))))
  --   --       coind = CohStruct↑ (P // ⟪ M ⟫) (RelOver Q ⟪ M ⟫) (M ⇙ Ψ C) (H C)

  --   --       need : CohStruct (SlcMgm (SubInvar↑ Q ⟪ M ⟫ (Ψ C)) ⇙ (Blorp Q M C))
  --   --       need = {!!}

  --     --   (ΣPoly P Q // Rel↑ R) ≃ (ΣPoly (P // R) (RelOver P R Q))
