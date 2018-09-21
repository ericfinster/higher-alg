{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Substitution
open import SubstCoh
open import OpetopicType

module Monad where

  record is-algebraic {ℓ} {I : Type ℓ} {P : Poly I} {R : PolyRel P} (X : OpetopicType P R) : Type ℓ where
    coinductive
    field

      is-mult : is-multiplicative P (ΣR R (Ref X))
      hom-is-alg : is-algebraic (Hom X)

  open is-algebraic public
  
  -- Some basic coherences
  module _ {ℓ} {I : Type ℓ} {P : Poly I} {R : PolyRel P}
    (T : OpetopicType P R) (is-alg : is-algebraic T) where

    μ : {i : I} (w : W P i) → Op P i
    μ w = fst (contr-center (is-mult is-alg w))

    η : (i : I) → Op P i
    η i = μ (lf i)

    WitRel : PolyRel P 
    WitRel = ΣR R (Ref T) 

    CohRel : PolyRel (P // WitRel)
    CohRel = ΣR (FlattenRel WitRel) (Ref (Hom T))

    μ-coh : {i : I} {f : Op P i} (w : W (P // WitRel) (i , f)) → Op (P // WitRel) (i , f)
    μ-coh w = fst (contr-center (is-mult (hom-is-alg is-alg) w))

    -- Nice!  So this is now completely general!!
    μ-flatten : {i : I} {f : Op P i} (w : W (P // WitRel) (i , f)) → μ (flatten WitRel w) == f
    μ-flatten {i} {f} pd = fst= (contr-path (is-mult is-alg (flatten WitRel pd)) lem₅)

      where lem₀ : Composite (P // WitRel) CohRel pd
            lem₀ = contr-center (is-mult (hom-is-alg is-alg) pd)

            lem₁ : flatten WitRel pd == fst (μ-coh pd)
            lem₁ = fst= (fst= (snd (fst (snd (snd lem₀))))) 

            lem₂ : flatten-frm WitRel pd == fst (snd (μ-coh pd)) [ (λ w₀ → Frame P w₀ f) ↓ lem₁ ]
            lem₂ = ↓-Σ-fst (snd= (fst= (snd (fst (snd (snd lem₀))))))
            
            lem₃ : WitRel (fst (μ-coh pd)) f (fst (snd (μ-coh pd)))
            lem₃ = snd (snd (μ-coh pd))

            lem₄ : WitRel (flatten WitRel pd) f (flatten-frm WitRel pd) 
            lem₄ = transport! (λ x → WitRel (fst x) f (snd x)) (pair= lem₁ lem₂) lem₃

            lem₅ : Composite P WitRel (flatten WitRel pd)
            lem₅ = f , flatten-frm WitRel pd , lem₄ 

    unit-r : (i : I) (f : Op P i) → μ (corolla P f) == f
    unit-r i f = μ-flatten (lf (i , f))


  -- Okay, our goal is to implement the idea you had last night for
  -- the monad structure on the universe.  Let's start by trying to
  -- work with the terminal type and we can generalize later.
  module _ {ℓ} {I : Type ℓ} (P : Poly I) (R : PolyRel P) where

    private
      R₀ = ΣR R (TRef R)
      R₁ = ΣR (FlattenRel R₀) (TRef (FlattenRel R₀))
      
    -- So, how is this going to work?
    postulate

      good : {i : I} {f : Op P i} (pd : W (P // R₀) (i , f))
        → is-contr (R (flatten R₀ pd) f (flatten-frm R₀ pd))

    P//R₀-is-multiplicative : is-multiplicative (P // R₀) (↑ (FlattenRel R₀))
    P//R₀-is-multiplicative pd = equiv-preserves-level (eqv ⁻¹)
      ⦃ Σ-level (good pd) (λ r₀ → Σ-level
        (Lift-level Unit-level) (λ _ → Lift-level Unit-level)) ⦄

      where eqv : Composite (P // R₀) (↑ (FlattenRel R₀)) pd ≃ Coherence P R (TRef R) (TRef (FlattenRel R₀)) pd
            eqv = comp-to-coh-eqv P R (TRef R) (TRef (FlattenRel R₀)) pd 

    -- Hmmm.  Maybe you made a mistake....
    -- Fuck. Yeah, I think again you didn't realize that the
    -- composite space there needs the element of R₁, which is
    -- what you are trying to show is contractible. FUCK FUCK FUCK!!!

    -- Okay, but back up one step: you know this type is inhabited.
    -- If you have two of them, then, you learn that w is a composite
    -- of coh in these two different ways.

    -- I mean, I still think your idea is a good one: use contractibility
    -- of some other space equivalent to this guy and probably coming from
    -- the monad structure to say that the globularity identification is
    -- unique.

    -- Right.  I still don't quite see it.

    -- Now, I want to use this to show that R₁, evaluated at a flatten is
    -- itself contractible.  This says that the property of being good is
    -- inherited by the hom.

    R₁-good₀ : {f : Ops P} (w : Op (P // R₀) f) (coh : W ((P // R₀) // R₁) (f , w))
      → is-contr (R₁ (flatten R₁ coh) w (flatten-frm R₁ coh))
    R₁-good₀ {f} w coh = Σ-level
                          (Σ-level
                           (Σ-level (good (flatten R₁ coh)) (λ _ → Lift-level Unit-level))
                           (λ r₀ → {!!}))
                          λ _ → Lift-level Unit-level

    R₁-good : {f : Ops P} (w : Op (P // R₀) f) (coh : W ((P // R₀) // R₁) (f , w))
      → is-contr (R₁ (flatten R₁ coh) w (flatten-frm R₁ coh))
    R₁-good {f} w coh = Σ-level (Σ-level (Σ-level (good (flatten R₁ coh)) (λ _ → Lift-level Unit-level))
      (λ r₀ → =-preserves-level {A = A} (equiv-preserves-level ceqv ⦃ P//R₀-is-multiplicative (flatten R₁ coh) ⦄ )))
      (λ _ → Lift-level Unit-level)

      where A : Type ℓ
            A = Σ (Op (P // R₀) f) (Frame (P // R₀) (flatten R₁ coh))

            eqv : Composite (P // R₀) R₁ (flatten R₁ coh) ≃ Coherence P R (TRef R) (TRef (FlattenRel R₀)) (flatten R₁ coh)
            eqv = comp-to-coh-eqv P R (TRef R) (TRef (FlattenRel R₀)) (flatten R₁ coh) 

            eqv₁-to : Coherence P R (TRef R) (TRef (FlattenRel R₀)) (flatten R₁ coh) → A
            eqv₁-to (r₀ , lift tt , lift tt) = {!s₁!}

            eqv₁ : Coherence P R (TRef R) (TRef (FlattenRel R₀)) (flatten R₁ coh) ≃ A
            eqv₁ = {!!}
            
            ceqv : Composite (P // R₀) R₁ (flatten R₁ coh) ≃ A
            ceqv = Σ-emap-r (λ op → {!!})

    -- Coherence : {i : I} {f : Op P i} (pd : W (P // R₀) (i , f)) → Type ℓ
    -- Coherence {i} {f} pd = Σ (R (flatten R₀ pd) f (flatten-frm R₀ pd)) (λ r₀ →
    --   Σ (X (flatten R₀ pd) f (flatten-frm R₀ pd) r₀) (λ s₀ →
    --      Y pd (flatten R₀ pd , flatten-frm R₀ pd , r₀ , s₀)
    --           (bd-frame R₀ pd) ((r₀ , s₀) , idp)))  


    -- Fuck, is it okay or not?


  -- FlattenRel : PolyRel (P // R)
  -- FlattenRel {i , f} pd (w , α , r) β = Σ (R (flatten R pd) f (flatten-frm R pd))
  --   (λ s → Path {A = Σ (Op (P // R) (i , f)) (Frame (P // R) pd) }
  --     ((flatten R pd , flatten-frm R pd , s) , bd-frame R pd)
  --     ((w , α , r) , β))




    -- Composite : (R : PolyRel) {i : I} (w : W i) → Type ℓ
    -- Composite R {i} w = Σ (Op P i) (λ f → Σ (Frame w f) (R w f))

    -- private
    --   R₀ = ΣR R X
    --   R₁ = ΣR (FlattenRel R₀) Y
    
    -- Coherence : {i : I} {f : Op P i} (pd : W (P // R₀) (i , f)) → Type ℓ
    -- Coherence {i} {f} pd = Σ (R (flatten R₀ pd) f (flatten-frm R₀ pd)) (λ r₀ →
    --   Σ (X (flatten R₀ pd) f (flatten-frm R₀ pd) r₀) (λ s₀ →
    --      Y pd (flatten R₀ pd , flatten-frm R₀ pd , r₀ , s₀)
    --           (bd-frame R₀ pd) ((r₀ , s₀) , idp)))  

    -- comp-to-coh-eqv : {i : I} {f : Op P i} (pd : W (P // R₀) (i , f))
    --   → Composite (P // R₀) R₁ pd ≃ Coherence pd
    -- comp-to-coh-eqv pd = equiv (to pd) (from pd) (to-from pd) (from-to pd)
