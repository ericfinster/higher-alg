{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Substitution
open import PolyMonad

-- Defining algebras
module wip.Algebra where

  module _ {ℓ} {I : Type ℓ} (P : Poly I) (X : I → Type ℓ) where

    -- Pulling back a polynomial along a family
    PbPoly : Poly (Σ I X)
    Op PbPoly (i , x) = ⟦ P ⟧ X i
    Param PbPoly (f , ϕ) (j , y) = Σ (Param P f j) (λ p → ϕ j p == y)

    -- erase all the intermediate decorations
    erase : {i : I} {x : X i} → W PbPoly (i , x) → W P i
    erase {i} {x} (lf ._) = lf i
    erase {i} {x} (nd ((f , ρ) , ϕ)) =
      let ϕ' j p = erase (ϕ (j , ρ j p) (p , idp))
      in nd (f , ϕ')

    -- find an erased leaf
    erase-lf : {i : I} {x : X i} (w : W PbPoly (i , x))
      → (j  : I) (y : X j)
      → Leaf PbPoly w (j , y) → Leaf P (erase w) j
    erase-lf (lf (i , x)) j y l = fst= l
    erase-lf (nd ((f , ρ) , ϕ)) j y ((k , ._) , (p , idp) , l) = 
      k , p , erase-lf (ϕ (k , ρ k p) (p , idp)) j y l

    -- retrieve the decoration at the leaves
    erase-dec : {i : I} {x : X i} (w : W PbPoly (i , x))
      → (j : I) (l : Leaf P (erase w) j) → X j
    erase-dec (lf (i , x)) j l = transport X l x
    erase-dec (nd ((f , ρ) , ϕ)) j (k , p , l) =
      erase-dec (ϕ (k , ρ k p) (p , idp)) j l

    -- the value at the erased leaf is the expected one
    erase-coh : {i : I} {x : X i} (w : W PbPoly (i , x))
      → (j  : I) (y : X j) (l : Leaf PbPoly w (j , y))
      → erase-dec w j (erase-lf w j y l) == y
    erase-coh (lf (i , x)) j y l = to-transp (snd= l)
    erase-coh (nd ((f , ρ) , ϕ)) j y ((k , ._) , (p , idp) , l) =
      erase-coh (ϕ (k , ρ k p) (p , idp)) j y l

    erase-lf-eqv : {i : I} {x : X i} (w : W PbPoly (i , x))
      → (j  : I) (y : X j)
      → Leaf PbPoly w (j , y) ≃ Σ (Leaf P (erase w) j) (λ l → y == erase-dec w j l)
    erase-lf-eqv w j y = {!!}

    erase-frame : {i : I} {x : X i}
      → (f : Op P i) (δ : Decor P f X)
      → (w : W PbPoly (i , x)) (β : Frame PbPoly w (f , δ))
      → Frame P (erase w) f
    erase-frame f δ w β j = equiv to {!!} {!!} {!!}

      where to : Leaf P (erase w) j → Param P f j
            to l = fst (–> (β (j , erase-dec w j l)) (<– (erase-lf-eqv w j (erase-dec w j l)) (l , idp)))

            -- ... and so on ...

    PbRel : PolyRel P → PolyRel PbPoly
    PbRel R ((i , x) , (f , δ)) (w , α) = R (i , f) (erase w , erase-frame f δ w α)

    -- Right, so now, is it true that a substitution invariant relation
    -- remains so in the pullback?  Well, I mean, yes.  I see: the reason
    -- is that pulling back is also a homomorphism for flatn and the
    -- associated frames.  Hence, since the relation is determined
    -- by the underlying relation R after erasing, the fact that this
    -- commutes means that the pullback of R is also subdivision invariant.

    -- Okay, we're getting closer.... so the first idea is to define a family

    -- Okay, have to prove these guys ... don't see
    -- any way around it.
    PbMagma : PolyMagma P → PolyMagma PbPoly
    PbMagma M = {!!}

    PbSubInvar : {M : PolyMagma P} → SubInvar ⟪ M ⟫ → SubInvar ⟪ PbMagma M ⟫
    PbSubInvar Ψ = {!!}

  PbCoh : ∀ {ℓ} {I : Type ℓ} {P : Poly I} (X : I → Type ℓ)
    → {M : PolyMagma P} (C : CohStruct M)
    → CohStruct (PbMagma P X M)
  Ψ (PbCoh {P = P} X {M = M} C) = PbSubInvar P X (Ψ C)
  H (PbCoh X C) = {!PbCoh ? (H C)!}

  -- We only need the polynomial structure
  -- to define what we mean by a magma ...
  AlgMap : ∀ {ℓ} {I : Type ℓ} (P : Poly I) (X : I → Type ℓ) → Type ℓ
  AlgMap {I = I} P X = (i : I) → ⟦ P ⟧ X i → X i

  -- And now, the definition of an algebra is that its an algebra
  -- map, together with and algebra map for the equality relation
  -- on the slice of the pullback.

  record PolyAlg {ℓ} {I : Type ℓ} (P : Poly I) (M : PolyMagma P) (C : CohStruct M) (X : I → Type ℓ) : Type ℓ where
    coinductive
    field

      ν : (i : I) → ⟦ P ⟧ X i → X i
      ν-co : PolyAlg (PbPoly P X // ⟪ PbMagma P X M ⟫)
                     (SlcMgm (Ψ (PbCoh X C)))
                     (H (PbCoh X C))
                     λ { ((i , x) , (f , δ)) → ν i (f , δ) == x }

  -- Perfect!
  
  -- There is, of course, also a completeness
  -- condition that you could add....
