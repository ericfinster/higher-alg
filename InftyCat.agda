{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Poly
open import PolyMonads
open import OpetopicTypes

module InftyCat where

  -- Uh, yeah, maybe we bring back the identity ...
  ∞CatMnd : (Ob : Type₀) → Mnd ((Σ ⊤ (cst Ob)) × (Σ ⊤ (λ u → (p : ρ (id ⊤) u) → Ob )))
  ∞CatMnd Ob = slc (pb (id ⊤) (λ { unit → Ob }))

  ∞Cat : Type₁
  ∞Cat = Σ Type₀ (λ Ob → ∞Alg (slc (pb (id ⊤) (λ { unit → Ob }))))

  module _ (Ob : Type₀) (Mor : ∞Alg (∞CatMnd Ob)) where

    open OpType (fst Mor)
    
    Hom : Ob → Ob → Type₀
    Hom x y = Ops ((unit , x) , (unit , cst y))

    comp : {x y z : Ob} → Hom x y → Hom y z → Hom x z
    comp {x} {y} {z} f g = filler-of CompNiche (snd Mor)

      where CompNiche : Niche (fst Mor) ((unit , x) , unit , cst z) 
            CompNiche = box {i = unit , x} (unit , λ { unit → y }) (λ { unit → unit , (λ { unit → z })})
                          (λ { unit → box (unit , λ { unit → z }) (λ { unit → unit , λ { unit → z } }) (λ { unit → dot (unit , z) })}) ,
                          λ { (inl unit) → f ;
                              (inr (unit , inl unit)) → g ;
                              (inr (unit , inr (unit , ()))) }


  -- A∞-Mnd : Mnd (⊤ × ⊤)
  -- A∞-Mnd = slc (id ⊤)

  -- module A∞Spaces (X : ∞Alg A∞-Mnd) where

  --   X₀ : Type₀
  --   X₀ = Ops (fst X) (unit , unit)
    
  --   mult : X₀ → X₀ → X₀
  --   mult x y = filler-of mult-niche (snd X)
    
  --     where mult-niche : Niche (fst X) (unit , unit)
  --           mult-niche = (box unit (λ _ → unit) (λ _ → box unit (λ _ → unit) (λ _ → dot unit))) ,
  --                        λ { (inl unit) → x ;
  --                            (inr (unit , inl unit)) → y ;
  --                            (inr (unit , inr (unit , ()))) }

    -- data Nst : {i : I} → (c : γ M i) → Type₀ where
    --   dot : (i : I) → Nst (η M i)
    --   box : {i : I} (c : γ M i)
    --         (δ : (p : ρ M c) → γ M (τ M p))
    --         (ε : (p : ρ M c) → Nst (δ p)) →
    --         Nst (μ M c δ)




  -- A∞-Mnd : Mnd (⊤ × ⊤)
  -- A∞-Mnd = slc (id ⊤)

  -- module A∞Spaces (X : ∞Alg A∞-Mnd) where

  --   X₀ : Type₀
  --   X₀ = Ops (fst X) (unit , unit)
    
  --   mult : X₀ → X₀ → X₀
  --   mult x y = filler-of mult-niche (snd X)
    
  --     where mult-niche : Niche (fst X) (unit , unit)
  --           mult-niche = (box unit (λ _ → unit) (λ _ → box unit (λ _ → unit) (λ _ → dot unit))) ,
  --                        λ { (inl unit) → x ;
  --                            (inr (unit , inl unit)) → y ;
  --                            (inr (unit , inr (unit , ()))) }
