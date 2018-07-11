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
  
  record is-algebraic {I : Type₀} {P : Poly I} (X : PSet P) : Type₁ where
    coinductive
    field

      has-fillers : {i : I} (w : W P i)
        → is-contr (Σ (γₚ P i) (λ c → Σ (ρ-fr P i w ≃ ρₚ P i c) (λ e → Filler X c (w , e))))

      higher-has-fillers : is-algebraic (Higher X)

  open is-algebraic public
  
  module _ {I : Type₀} {P : Poly I} (O : PSet P) (is-alg : is-algebraic O) where

    μ : {i : I} (w : W P i) → γₚ P i
    μ w = fst (fst (has-level-apply (has-fillers is-alg w))) 

    μ-plc-eqv : {i : I} (w : W P i) → leaves P w ≃ ρₚ P i (μ w)
    μ-plc-eqv w = fst (snd (fst (has-level-apply (has-fillers is-alg w)))) 

    μ-witness : {i : I} (w : W P i) → Filler O (μ w) (w , μ-plc-eqv w)
    μ-witness w = snd (snd (fst (has-level-apply (has-fillers is-alg w)))) 

    η : (i : I) → γₚ P i
    η i = μ (lf i)

    unary-op : (i : I) → Type₀
    unary-op i = Σ (γₚ P i) (λ c → is-contr (ρₚ P i c))

    u-domain : {i : I} (u : unary-op i) → I
    u-domain {i} (c , e) = τₚ P i c (fst (has-level-apply e))

    Arrow : I → I → Type₀
    Arrow i j = Σ (unary-op j) (λ u → u-domain u == i)

    Comp : (i j k : I) → Arrow i j → Arrow j k → Arrow i k
    Comp i j k ((f , α) , x) ((g , β) , y) = (c , {!!}) , {!!}

      where c : γₚ P k
            c = μ (nd k (g , λ p → transport (W P) (! y ∙ ap (τₚ P k g) (snd (has-level-apply β) p))
                   (nd j (f , (λ q → lf (τₚ P j f q)))))) 
            
    l-inv : {i : I} (u : unary-op i) → Type₀
    l-inv {i} u = Σ (Arrow j i) (λ l → fst (fst (Comp i j i {!u!} l)) == η i)

      where j = u-domain u

            lu : (l : γₚ P j) → γₚ P i
            lu l = μ (nd {!j!} {!!})
