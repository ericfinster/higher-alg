{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Inspect

module Poly where

  record Poly (I : Type₀) : Type₁ where
    field
      γ : I → Type₀
      ρ : {i : I} (c : γ i) (j : I) → Type₀

  open Poly public

  ⟦_⟧ : {I : Type₀} (P : Poly I) → (I → Set) → I → Set
  ⟦ P ⟧ X i = Σ (γ P i) (λ c → ∀ j → (p : ρ P c j) → X j)

  module _ {I : Type₀} (P : Poly I) where
  
    data W : I → Type₀ where
      lf : (i : I) → W i
      nd : {i : I} → ⟦ P ⟧ W i → W i

    data Leaf : {i : I} (w : W i) → I → Type₀ where
      leaf : (i : I) → Leaf (lf i) i
      stem : {i : I} (c : γ P i)
        → (δ : ∀ j → (p : ρ P c j) → W j)
        → {j : I} → (p : ρ P c j)
        → {k : I} → Leaf (δ j p) k
        → Leaf (nd (c , δ)) k

    data Node : {i : I} (w : W i) {j : I} (c : γ P j) → Type₀ where
      this : {i : I} (c : γ P i)
        → (δ : ∀ j → (p : ρ P c j) → W j)
        → Node (nd (c , δ)) c
      that : {i : I} (c : γ P i)
        → (δ : ∀ j → (p : ρ P c j) → W j)
        → {j : I} → (p : ρ P c j)
        → {k : I} → {d : γ P k} → Node (δ j p) d
        → Node (nd (c , δ)) d

    lf-lf-contr : (i : I) → is-contr (Σ I (Leaf (lf i)))
    lf-lf-contr i = has-level-in ((i , leaf i) , λ { (_ , leaf .i) → idp })
    
    corolla : {i : I} (c : γ P i) → W i
    corolla {i} c = nd (c , λ j p → lf j)

    corolla-lf-eqv : {i : I} (c : γ P i)
      → (j : I) → Leaf (corolla c) j ≃ ρ P c j
    corolla-lf-eqv c j = equiv to from (λ _ → idp) from-to

      where to : Leaf (corolla c) j → ρ P c j
            to (stem c _ p (leaf i)) = p

            from : ρ P c j → Leaf (corolla c) j
            from p = stem c _ p (leaf j)

            from-to : (l : Leaf (corolla c) j) → from (to l) == l
            from-to (stem c _ p (leaf i)) = idp

  --   -- Annoying.  I seem to blow a bubble.  But I don't think
  --   -- it should be there.  Can you get rid of it?
  --   corolla-unique : {i : I} (c : γ P i) (w : W i)
  --     → (is-c : is-contr (node w))
  --     → (pth : node-type w (contr-center is-c) == (i , c))
  --     → corolla c == w 
  --   corolla-unique c (lf i) is-c pth = ⊥-elim (contr-center is-c)
  --   corolla-unique c (nd i (c' , δ)) is-c pth = ap corolla {!!} ∙ and-so

  --     where lem : (i , c') == (i , c)
  --           lem = (! (ap (λ x → node-type (nd i (c' , δ)) x) (contr-path is-c (inl unit)))) ∙ pth

  --           must-be-leaves : (p : ρ P i c') → δ p == lf (τ P i c' p)
  --           must-be-leaves p with δ p | inspect δ p
  --           must-be-leaves p | lf .(τ P i c' p) | ingraph e = idp
  --           must-be-leaves p | nd .(τ P i c' p) _ | ingraph e = ⊥-elim
  --             (inl≠inr unit no-no (contr-has-all-paths ⦃ is-c ⦄ (inl unit) (inr no-no))) 

  --             where no-no : Σ (ρ P i c') (node ∘ δ)
  --                   no-no = p , transport! node e (inl unit)

  --           and-so : corolla c' == nd i (c' , δ)
  --           and-so = ap (λ d → nd i (c' , d)) (λ= (λ p → ! (must-be-leaves p)))

  module _ {I : Type₀} (P : Poly I) where

    Fr : Poly I
    γ Fr = W P
    ρ Fr w = Leaf P w

    graft : {i : I} (w : W P i) (ε : ∀ j → Leaf P w j → W P j) → W P i
    graft (lf i) ε = ε i (leaf i)
    graft (nd (c , δ)) ε = nd (c , λ j p → graft (δ j p) (λ k l → ε k (stem c δ p l)))

    -- graft-leaf-to : {i : I} (w : W P i) (ε : ∀ j → Leaf P w j → W P j)
    --   → (ll : Σ (Σ I (Leaf P w)) (λ { (k , l) → Σ I (Leaf P (ε k l)) }))
    --   → Leaf P (graft w ε) (fst (snd ll))
    -- graft-leaf-to = {!!}
    
  --   μρ-to-fr : (i : I) (w : W P i)
  --     → (δ : (p : ρ-fr i w) → W P (τ-fr i w p))
  --     → Σ (ρ-fr i w) (λ p → ρ-fr (τ-fr i w p ) (δ p))
  --     → ρ-fr i (μ-fr i w δ)
  --   μρ-to-fr i (lf .i) δ (unit , p₁) = p₁
  --   μρ-to-fr i (nd .i (c , δ₀)) δ ((p₀ , p₁) , p₂) = p₀ , μρ-to-fr (τ P i c p₀) (δ₀ p₀) (λ p₃ → δ (p₀ , p₃)) (p₁ , p₂)

  --   μρ-from-fr : (i : I) (w : W P i)
  --     → (δ : (p : ρ-fr i w) → W P (τ-fr i w p))
  --     → ρ-fr i (μ-fr i w δ)
  --     → Σ (ρ-fr i w) (λ p → ρ-fr (τ-fr i w p) (δ p))
  --   μρ-from-fr i (lf .i) δ p = unit , p
  --   μρ-from-fr i (nd .i (c , δ₀)) δ (p₀ , p₁) =
  --     let pp = μρ-from-fr (τ P i c p₀) (δ₀ p₀) (λ p₂ → δ (p₀ , p₂)) p₁
  --     in (p₀ , fst pp) , snd pp

  --   μρ-to-from-fr : (i : I) (w : W P i)
  --     → (δ : (p : ρ-fr i w) → W P (τ-fr i w p))
  --     → (p : ρ-fr i (μ-fr i w δ))
  --     → μρ-to-fr i w δ (μρ-from-fr i w δ p) == p
  --   μρ-to-from-fr i (lf .i) δ p = idp
  --   μρ-to-from-fr i (nd .i (c , δ₀)) δ (p₀ , p₁) = 
  --     let ih = μρ-to-from-fr (τ P i c p₀) (δ₀ p₀) (λ p₂ → δ (p₀ , p₂)) p₁
  --     in ap (λ p₂ → p₀ , p₂) ih

  --   μρ-from-to-fr : (i : I) (w : W P i)
  --     → (δ : (p : ρ-fr i w) → W P (τ-fr i w p))
  --     → (p : Σ (ρ-fr i w) (λ p → ρ-fr (τ-fr i w p ) (δ p)))
  --     → μρ-from-fr i w δ (μρ-to-fr i w δ p) == p
  --   μρ-from-to-fr i (lf .i) δ (unit , p₁) = idp
  --   μρ-from-to-fr i (nd .i (c , δ₀)) δ ((p₀ , p₁) , p₂) =
  --     let ih = μρ-from-to-fr (τ P i c p₀) (δ₀ p₀) (λ p₃ → δ (p₀ , p₃)) (p₁ , p₂)
  --         ρ-fr-δ x = ρ-fr (τ-fr (τ P i c (fst x)) (δ₀ (fst x)) (snd x)) (δ x)
  --     in pair= (pair= idp (fst= ih)) (↓-ap-in ρ-fr-δ (λ x → (p₀ , x)) (snd= ih))

  --   μρ-equiv-fr : (i : I) (w : W P i)
  --     → (δ : (p : ρ-fr i w) → W P (τ-fr i w p))
  --     → Σ (ρ-fr i w) (λ p → ρ-fr (τ-fr i w p ) (δ p))
  --       ≃' ρ-fr i (μ-fr i w δ)
  --   μρ-equiv-fr i w δ =
  --     equiv' (μρ-to-fr i w δ) (μρ-from-fr i w δ)
  --            (μρ-to-from-fr i w δ) (μρ-from-to-fr i w δ)


