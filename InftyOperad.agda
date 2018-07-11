{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Poly

module InftyOperad where

  module _ {I : Type₀} (P : Poly I) where
  
    leaves : {i : I} → W P i → Type₀
    leaves {i} w = ρ-fr P i w

    nodes : {i : I} → W P i → Type₀
    nodes (lf i) = ⊥
    nodes (nd i (c , δ)) = ⊤ ⊔ Σ (ρₚ P i c) (nodes ∘ δ) 

    node-type : {i : I} (w : W P i) (n : nodes w) → Σ I (γₚ P)
    node-type (lf i) ()
    node-type (nd i (c , δ)) (inl unit) = i , c
    node-type (nd i (c , δ)) (inr (p , q)) = node-type (δ p) q

    p-frame : {i : I} (c : γₚ P i) → Type₀
    p-frame {i} c = Σ (W P i) (λ w → leaves w ≃ ρₚ P i c)
    
    FillPoly : (F : {i : I} (c : γₚ P i) → p-frame c → Type₀) → Poly (Σ I (γₚ P))
    γₚ (FillPoly F) (i , c) = Σ (p-frame c) (F c)
    ρₚ (FillPoly F) (i , c) ((w , e) , x) = nodes w
    τₚ (FillPoly F) (i , c) ((w , e) , x) n = node-type w n

  record PSet {I : Type₀} (P : Poly I) : Type₁ where
    coinductive
    field

      Filler : {i : I} (c : γₚ P i) → p-frame P c → Type₀
      Higher : PSet (FillPoly P Filler)

  open PSet public
  
  record is-∞-operad {I : Type₀} {P : Poly I} (X : PSet P) : Type₁ where
    coinductive
    field

      has-fillers : (i : I) (w : W P i)
        → is-contr (Σ (γₚ P i) (λ c → Σ (ρ-fr P i w ≃ ρₚ P i c) (λ e → Filler X c (w , e))))

      higher-has-fillers : is-∞-operad (Higher X)
