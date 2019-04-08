{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Grafting
open import Biased

module wip.BiasedRel {ℓ} {I : Type ℓ} (P : Poly I) (R : PolyRel P) where

  open import Substitution P
  open import wip.SubstSubst P
  open import wip.SubstUnits P
  open BiasedMgm
  open BiasedLaws

  -- The extra information required from a relation in order that we
  -- can construct a biased multiplication on the slice by R.
  record BiasedRel : Type ℓ where
    field

      η-rel : (f : Ops P) → R f (subst-η f)
        
      γ-rel : (f : Ops P) (wα : InFrame P f) (r : R f wα)
        → (κ : Decor (P // R) (wα , r) (Op (P // R)))
        → R f (subst-γ f wα (λ g n → fst (κ g n)))

  open BiasedRel
  
  BiasedRelToMgm : BiasedRel → BiasedMgm (P // R)
  η (BiasedRelToMgm SRel) f =
    subst-η f , η-rel SRel f
  η-frm (BiasedRelToMgm SRel) =
    subst-η-frm
  γ (BiasedRelToMgm SRel) {f} (wα , r) κ =
    let κ' g n = fst (κ g n)
    in subst-γ f wα κ' , γ-rel SRel f wα r κ
  γ-frm (BiasedRelToMgm SRel) ((w , α) , r) κ g =
    let κ' g n = fst (κ g n)
    in subst-node-eqv w κ' g

  record BiasedRelLaws (SRel : BiasedRel) : Type ℓ where
    field

      subst-unit-l-rel : {i : I} {f : Op P i}
        → (w : W P i) (α : Frame P w f) (r : R (i , f) (w , α))
        → γ-rel SRel (i , f) (w , α) r (λ g _ → η (BiasedRelToMgm SRel) g)
            == r [ R (i , f) ↓ pair= (subst-unit-l w) (subst-unit-l-frm w α) ]

      subst-unit-r-rel : {i : I} {f : Op P i}
        → (κ : (g : Ops P) → Node P (corolla P f) g → Op (P // R) g)
        → snd (κ (i , f) (inl idp)) == γ-rel SRel (i , f) (corolla P f , corolla-frm P f) (η-rel SRel (i , f)) κ
            [ R (i , f) ↓ pair= (graft-unit P (fst (fst ((κ (i , f) (inl idp)))))) (subst-unit-r-frm (λ g n → fst (κ g n))) ]

      subst-assoc-rel : {i : I} {f : Op P i}
        → (w : W P i) (α : Frame P w f) (r : R (i , f) (w , α))
        → (κ : (g : Ops P) → Node P w g → Op (P // R) g)
        → (ν : (g : Ops P) → Σ (Ops P) (λ h → Σ (Node P w h) (λ n → Node P (fst (fst (κ h n))) g)) → Op (P // R) g)
        → let κ' g n = fst (κ g n)
              ν' g t = fst (ν g t)
          in γ-rel SRel (i , f) (w , α) r (λ g n → subst-γ g (κ' g n) (λ g₁ n₁ → ν' g₁ (g , n , n₁)) ,
                                                   γ-rel SRel g (κ' g n) (snd (κ g n)) (λ g₁ n₁ → ν g₁ (g , n , n₁)))
             == γ-rel SRel (i , f) (subst-γ (i , f) (w , α) κ')
                                   (γ-rel SRel (i , f) (w , α) r κ)
                                   (λ g n → ν g (<– (subst-node-eqv w κ' g) n))
               [ R (i , f) ↓ pair= (subst-assoc w κ' ν') (subst-assoc-frm w α κ' ν') ]


  open BiasedRelLaws

  BiasedLawsToLaws : (SRel : BiasedRel) (SLaws : BiasedRelLaws SRel)
    → BiasedLaws (P // R) (BiasedRelToMgm SRel)
  unit-l (BiasedLawsToLaws SRel SLaws) ((w , α) , r) =
    pair= (pair= (subst-unit-l w) (subst-unit-l-frm w α))
          (subst-unit-l-rel SLaws w α r)
  unit-r (BiasedLawsToLaws SRel SLaws) {i , f} κ =
    let ((w , α) , r) = κ (i , f) (inl idp)
        κ' g n = fst (κ g n)
    in pair= (pair= (graft-unit P w) (subst-unit-r-frm κ'))
             (subst-unit-r-rel SLaws κ)
  assoc (BiasedLawsToLaws SRel SLaws) {i , f} ((w , α) , r) κ ν = 
    let κ' g n = fst (κ g n)
        ν' g t = fst (ν g t)
    in pair= (pair= (subst-assoc w κ' ν') (subst-assoc-frm w α κ' ν'))
             (subst-assoc-rel SLaws w α r κ ν)
  unit-l-frm (BiasedLawsToLaws SRel SLaws) ((w , α) , r) g n =
    ↓-Σ-weaken (λ x → Node P (fst x) g)
      (↓-Σ-weaken (λ x → Node P x g)
                  (subst-node-unit-l w g n))
  unit-r-frm (BiasedLawsToLaws SRel SLaws) {i , f} κ g n =
    ↓-Σ-weaken (λ x → Node P (fst x) g)
      (↓-Σ-weaken (λ x → Node P x g)
        (graft-unit-nd P (fst (fst (κ (_ , f) (inl idp)))) g n)) 
  assoc-frm (BiasedLawsToLaws SRel SLaws) ((w , α) , r) κ ν k g m h n o =
    let κ' g n = fst (κ g n)
        ν' g t = fst (ν g t)
    in ↓-Σ-weaken (λ x → Node P (fst x) k)
         (↓-Σ-weaken (λ x → Node P x k)
                     (subst-node-assoc w κ' ν' g h k m n o))
