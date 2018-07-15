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
      this : (i : I) → Leaf (lf i) i
      that : {i : I} (c : γ P i)
        → (δ : ∀ j → (p : ρ P c j) → W j)
        → {j : I} → (p : ρ P c j)
        → {k : I} → Leaf (δ j p) k
        → Leaf (nd (c , δ)) k

    data Node : {i : I} (w : W i) {j : I} (c : γ P j) → Type₀ where
      here : {i : I} (c : γ P i)
        → (δ : ∀ j → (p : ρ P c j) → W j)
        → Node (nd (c , δ)) c
      there : {i : I} (c : γ P i)
        → (δ : ∀ j → (p : ρ P c j) → W j)
        → {j : I} → (p : ρ P c j)
        → {k : I} → {d : γ P i} → Node (δ j p) d
        → Node (nd (c , δ)) d

    lf-lf-contr : (i : I) → is-contr (Σ I (Leaf (lf i)))
    lf-lf-contr i = has-level-in ((i , this i) , λ { (_ , this .i) → idp })
    
    corolla : {i : I} (c : γ P i) → W i
    corolla {i} c = nd (c , λ j p → lf j)
    
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

  --   -- bleep : (i : I) (p : Σ I (γ P)) (w : W i)
  --   --   → (is-c : is-contr (node w))
  --   --   → (pth : node-type w (contr-center is-c) == p)
  --   --   → (q : i == fst p)
  --   --   → corolla (snd p) == transport W q w
  --   -- bleep i .(node-type (lf i) (fst (has-level-apply is-c))) (lf .i) is-c idp q = {!!}
  --   -- bleep i .(node-type (nd i x) (fst (has-level-apply is-c))) (nd .i x) is-c idp q = {!!}

  --   -- and-then : {i : I} (c : γ P i) (w : W i)
  --   --   → (is-c : is-contr (node w))
  --   --   → (pth : node-type w (contr-center is-c) == (i , c))
  --   --   → corolla c == w
  --   -- and-then {i} c w is-c pth = bleep i (i , c) w is-c pth idp

  Fr : {I : Type₀} (P : Poly I) → Poly I
  γ (Fr P) = W P
  ρ (Fr P) w = Leaf P w

  module _ {I : Type₀} (P : Poly I) where

    γ-fr : I → Type₀
    γ-fr = γ (Fr P)

    ρ-fr : {i : I} (w : W P i) → I → Type₀
    ρ-fr = ρ (Fr P)

    η-fr : (i : I) → γ-fr i
    η-fr = lf

    graft : {i : I} (w : W P i) (ε : ∀ j → Leaf P w j → W P j) → W P i
    graft (lf i) ε = ε i (this i)
    graft (nd (c , δ)) ε = nd (c , λ j p → graft (δ j p) (λ k l → ε k (that c δ p l)))
    
    -- {-# TERMINATING #-}
    -- graft : {i : I} → ⟦ Fr P ⟧ (W P) i → W P i
    -- graft {i} (lf i , ε) = ε i (this i)
    -- graft {i} (nd (c , δ) , ε) = nd (c , λ j p → graft (δ j p , λ k l → ε k (that c δ p l)))

  --   μ-fr : (i : I) (c : γ-fr i) (δ : (p : ρ-fr i c) → γ-fr (τ-fr i c p)) → γ-fr i
  --   μ-fr i (lf .i) δ = δ unit
  --   μ-fr i (nd .i (c , δ₀)) δ = nd i (c , λ p₀ → μ-fr (τ P i c p₀) (δ₀ p₀) (λ p₁ → δ (p₀ , p₁)))

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


  -- ZeroPoly : (I : Type₀) → Poly I
  -- γ  (ZeroPoly I) i = ⊥
  -- ρ (ZeroPoly I) i () 
  -- τ (ZeroPoly I) i () _
