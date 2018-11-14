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

    -- Okay, have to prove these guys ... don't see
    -- any way around it.
    PbMagma : PolyMagma P → PolyMagma PbPoly
    PbMagma M = {!!}

    PbSubInvar : {M : PolyMagma P} → SubInvar (MgmRel M) → SubInvar (MgmRel (PbMagma M))
    PbSubInvar Ψ = {!!}

  -- And bingo, you arrive at the main point:
  -- you need to know that pulling back and
  -- slicing commute for some appropriate choice
  -- of fibration.


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
      ν-co : PolyAlg (PbPoly P X // MgmRel (PbMagma P X M))
                     (SlcMgm (Ψ (PbCoh X C)))
                     (H (PbCoh X C))
                     λ { ((i , x) , (f , δ)) → ν i (f , δ) == x }

  -- Perfect!
  
  -- There is, of course, also a completeness
  -- condition that you could add....
