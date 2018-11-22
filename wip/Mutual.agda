{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Substitution
open import PolyMonad

-- A mutual definition of monads and algebras
module wip.Mutual {ℓ} where

  module _ {I : Type ℓ} (P : Poly I) where

    -- The substituion polynomial
    SubstPoly : Poly (Ops P)
    Op SubstPoly = InFrame P
    Param SubstPoly (w , _) = Node P w

    -- Pulling back a polynomial along a family
    PbPoly : (X : I → Type ℓ) → Poly (Σ I X)
    Op (PbPoly X) (i , x) = ⟦ P ⟧ X i
    Param (PbPoly X) (f , ϕ) (j , y) = Σ (Param P f j) (λ p → ϕ j p == y)

  CohData : {I : Type ℓ} {P : Poly I} (M : PolyMagma P) → Type ℓ

  PolyMonad : {I : Type ℓ} (P : Poly I) → Type ℓ
  PolyMonad P = Σ (PolyMagma P) (CohData)

  SubstMnd : {I : Type ℓ} (P : Poly I) → PolyMonad (SubstPoly P)
  Slice : {I : Type ℓ} {P : Poly I} (M : PolyMonad P) → PolyMonad (P // MgmRel (fst M))
  Pb : {I : Type ℓ} {P : Poly I} (M : PolyMonad P) (X : I → Type ℓ) → PolyMonad (PbPoly P X)

  record PolyAlg {I : Type ℓ} {P : Poly I} (M : PolyMonad P) (X : I → Type ℓ) : Type ℓ

  CohData {P = P} M = PolyAlg (Slice (SubstMnd P))
    (λ { ((i , f) , (w , α)) → MgmRel M (i , f) (w , α) })

  record PolyAlg {I} {P} M X where
    coinductive
    field

      ν : (i : I) → ⟦ P ⟧ X i → X i
      ν-coh : PolyAlg (Slice (Pb M X))
        (λ { ((i , x) , (f , δ)) → ν i (f , δ) == x })

  open PolyAlg
  
  Slice (M , C) = (SlcMgm (λ pd → ν C {!!} ({!!} , {!!}))) , {!!}

  SubstMnd P = {!!}
  Pb M X = {!!}


  -- record PolyAlg {ℓ} {I : Type ℓ} (P : Poly I) (M : PolyMagma P) (C : CohStruct M) (X : I → Type ℓ) : Type ℓ where
  --   coinductive
  --   field

  --     ν : (i : I) → ⟦ P ⟧ X i → X i
  --     ν-co : PolyAlg (PbPoly P X // MgmRel (PbMagma P X M))
  --                    (SlcMgm (Ψ (PbCoh X C)))
  --                    (H (PbCoh X C))
  --                    λ { ((i , x) , (f , δ)) → ν i (f , δ) == x }

