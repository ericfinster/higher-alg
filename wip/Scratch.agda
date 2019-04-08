{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Grafting
open import Substitution
open import wip.PolyOver
open import wip.RelOver

module wip.Scratch {ℓ} where

  -- APoly : Poly (Lift {j = ℓ} ⊤)
  -- Op APoly _ = A
  -- Param APoly a (lift tt) = Lift ⊤

  -- postulate

  --   AMgm : PolyMagma APoly
  
  -- SPoly : Poly (Ops APoly)
  -- SPoly = APoly // ⟪ AMgm ⟫ 

  -- data ATr : Type ℓ where
  --   aleaf : A → ATr
  --   anode : List (ATr) → ATr

  -- {-# TERMINATING #-}
  -- lvs : ATr → List A
  -- lvs (aleaf a) = a :: nil
  -- lvs (anode ts) = concat (map lvs ts)

  -- to : (a : Ops APoly) → W SPoly a → ATr
  -- to (lift unit , a) (lf .(lift unit , a)) = aleaf a
  -- to (lift unit , .(μ AMgm _)) (nd (((_ , _) , idp) , ϕ)) = {!!}

  record ∞Mgm {I : Type ℓ} (P : Poly I) : Type ℓ where
    coinductive
    field

      Mgm : PolyMagma P 
      InfMgm : ∞Mgm (P // ⟪ Mgm ⟫)


  open ∞Mgm

  claim : {I : Type ℓ} (P : Poly I) (M : ∞Mgm P) (Q : PolyOver P) → ∞Mgm (ΣPoly (P // ⟪ Mgm M ⟫) (Q ⇑ ⟪ Mgm M ⟫) )
  μ (Mgm (claim P M Q)) w = μ (Mgm (InfMgm M)) (W↓ (Q ⇑ ⟪ Mgm M ⟫) w) , ({!!} , {!!}) , {!!}  -- μ (Mgm (InfMgm M))
  μ-frm (Mgm (claim P M Q)) = {!!}
  InfMgm (claim P M Q) = {!!}

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

