{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Poly

module InftyOperad where

  module _ {I : Type₀} (P : Poly I) where

    p-frame : {i : I} (c : γ P i) → Type₀
    p-frame {i} c = Σ (W P i) (λ w → leaf P w ≃ ρ P i c)
    
    FillPoly : (F : {i : I} (c : γ P i) → p-frame c → Type₀) → Poly (Σ I (γ P))
    γ (FillPoly F) (i , c) = Σ (p-frame c) (F c)
    ρ (FillPoly F) (i , c) ((w , e) , x) = node P w
    τ (FillPoly F) (i , c) ((w , e) , x) n = node-type P w n

  record PSet {I : Type₀} (P : Poly I) : Type₁ where
    coinductive
    field

      Filler : {i : I} (c : γ P i) → p-frame P c → Type₀
      Higher : PSet (FillPoly P Filler)

  open PSet public
  
  record is-algebraic {I : Type₀} {P : Poly I} (X : PSet P) : Type₁ where
    coinductive
    field

      has-fillers : {i : I} (w : W P i)
        → is-contr (Σ (γ P i) (λ c → Σ (leaf P w ≃ ρ P i c) (λ e → Filler X c (w , e))))

      higher-has-fillers : is-algebraic (Higher X)

  open is-algebraic public
  
  module _ {I : Type₀} {P : Poly I} (O : PSet P) (is-alg : is-algebraic O) where

    μ : {i : I} (w : W P i) → γ P i
    μ w = fst (fst (has-level-apply (has-fillers is-alg w))) 

    μ-plc-eqv : {i : I} (w : W P i) → leaf P w ≃ ρ P i (μ w)
    μ-plc-eqv w = fst (snd (fst (has-level-apply (has-fillers is-alg w)))) 

    μ-witness : {i : I} (w : W P i) → Filler O (μ w) (w , μ-plc-eqv w)
    μ-witness w = snd (snd (fst (has-level-apply (has-fillers is-alg w)))) 

    η : (i : I) → γ P i
    η i = μ (lf i)

    unary-op : (i : I) → Type₀
    unary-op i = Σ (γ P i) (λ c → is-contr (ρ P i c))

    u-domain : {i : I} (u : unary-op i) → I
    u-domain {i} (c , e) = τ P i c (fst (has-level-apply e))

    Arrow : I → I → Type₀
    Arrow i j = Σ (unary-op j) (λ u → u-domain u == i)

    Comp : (i j k : I) → Arrow i j → Arrow j k → Arrow i k
    Comp i j k ((f , α) , x) ((g , β) , idp) = (c , {!!}) , {!!}

      where c : γ P k
            c = μ (nd k (g , λ p → transport (W P) (ap (τ P k g) (snd (has-level-apply β) p))
                   (nd j (f , (λ q → lf (τ P j f q)))))) 

    l-inv : {i : I} (u : unary-op i) → Type₀
    l-inv {i} u = Σ (Arrow i j) (λ l → fst (fst (Comp j i j (u , idp) l)) == η j)

      where j = u-domain u

    r-inv : {i : I} (u : unary-op i) → Type₀
    r-inv {i} u = Σ (Arrow i j) (λ r → fst (fst (Comp i j i r (u , idp))) == η i)

      where j = u-domain u

    is-invertible : ∀ {i} (u : unary-op i) → Type₀
    is-invertible u = l-inv u × r-inv u
