{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Poly

module PolyDomain where

  Frame : {I : Type₀} (P : Poly I) {i : I} (w : W P i) (c : γ P i) → Type₀
  Frame {I} P w c = (j : I) → Leaf P w j ≃ ρ P c j

  _//_ : {I : Type₀} (P : Poly I) (F : {i : I} {w : W P i} {c : γ P i} → Frame P w c → Type₀) → Poly (Σ I (γ P))
  γ (P // F) (i , c) = Σ (W P i) (λ w → Σ (Frame P w c) F)
  ρ (P // F) (w , f , x) (j , d) = Node P w d

  record PolyDomain {I : Type₀} (P : Poly I) : Type₁ where
    coinductive
    field

      F : {i : I} {w : W P i} {c : γ P i} → Frame P w c → Type₀
      H : PolyDomain (P // F)

  open PolyDomain public

  --
  --  The Baez-Dolan substitution operation
  --

  module Substitution {I : Type₀} {P : Poly I} (D : PolyDomain P) where

    {-# TERMINATING #-}
    flatten : {i : I} (c : γ P i)
      → (tr : W (P // (F D)) (i , c))
      → W P i

    flatten-lf-eqv : {i : I} (c : γ P i)
      → (tr : W (P // (F D)) (i , c))
      → (j : I) → Leaf P (flatten c tr) j ≃ ρ P c j

    substitute : {i : I} (w : W P i)
      → (κ : (c : Σ I (γ P)) → Node P w (snd c) → W (P // F D) c)
      → W P i

    substitute-lf-eqv : {i : I} (w : W P i)
      → (κ : (c : Σ I (γ P)) → Node P w (snd c) → W (P // F D) c)
      → (j : I) → Leaf P (substitute w κ) j ≃ Leaf P w j

    flatten c (lf .(_ , c)) = corolla P c
    flatten c (nd ((w , f , x) , ε)) = substitute w ε

    flatten-lf-eqv c (lf .(_ , c)) j = corolla-lf-eqv P c j
    flatten-lf-eqv c (nd ((w , f , x) , ε)) j = f j ∘e substitute-lf-eqv w ε j

    substitute (lf i) κ = lf i
    substitute (nd {i} (c , δ)) κ =
      let tr = κ (i , c) (this c δ)
          p j l = –> (flatten-lf-eqv c tr j) l
      in graft P (flatten c tr) (λ j l → substitute (δ j (p j l)) (λ ic n → κ ic (that c δ (p j l) n)))

    substitute-lf-eqv (lf i) κ j = ide (Leaf P (lf i) j)
    substitute-lf-eqv (nd {i} (c , δ)) κ j = {!!}

    -- subst-lcl-lf-eqv (lf i) κ = ide ⊤
    -- subst-lcl-lf-eqv (nd i (c , δ)) κ = 
    --   Σ-emap-l (leaf P ∘ δ) (subst-lf-eqv c (κ true)) ∘e                         -- Equivalence on base
    --   Σ-emap-r (λ l → (leaf-inv-! P (δ (p l)) (subst-lf-coh c (κ true) l))⁻¹ ∘e  -- Equivalence by transport ...
    --     subst-lcl-lf-eqv (w' l) (κ' l)) ∘e                                       -- ... and Induction Hypothesis
    --   (graft-lf-eqv P i (subst c (κ true)) (λ l → subst-lcl (w' l) (κ' l)))⁻¹    -- Characterization of graft leaves
      
    --   where open SubstLcl c δ κ

    -- subst-lcl : {i : I} (w : W P i)
    --   → (κ : (n : node P w) → W (P // (F X)) (node-type P w n))
    --   → W P i

    -- subst-lf-eqv : {i : I} (c : γ P i)
    --   → (tr : W (P // (F X)) (i , c))
    --   → leaf P (subst c tr) ≃ ρ P i c

    -- subst-lf-coh : {i : I} (c : γ P i)
    --   → (tr : W (P // (F X)) (i , c))
    --   → (l : leaf P (subst c tr))
    --   → leaf-type P (subst c tr) l == τ P i c (–> (subst-lf-eqv c tr) l)

    -- subst-lcl-lf-eqv : {i : I} (w : W P i)
    --   → (κ : (n : node P w) → W (P // (F X)) (node-type P w n))
    --   → leaf P (subst-lcl w κ) ≃ leaf P w

    -- subst-lcl-lf-coh : {i : I} (w : W P i)
    --   → (κ : (n : node P w) → W (P // (F X)) (node-type P w n))
    --   → (l : leaf P (subst-lcl w κ))
    --   → leaf-type P (subst-lcl w κ) l == leaf-type P w (–> (subst-lcl-lf-eqv w κ) l)

    -- subst c (lf .(_ , c)) = corolla P c
    -- subst c (nd .(_ , c) ((w , _ , _) , ε)) = subst-lcl w ε

    -- module SubstLcl {i : I} (c : γ P i)
    --   (δ : (p : ρ P i c) → W P (τ P i c p))
    --   (κ : (n : node P (nd i (c , δ))) → W (P // (F X)) (node-type P (nd i (c , δ)) n))
    --   (l : leaf P (subst c (κ true))) where

    --   p : ρ P i c
    --   p = –> (subst-lf-eqv c (κ true)) l

    --   w' : W P (leaf-type P (subst c (κ true)) l)
    --   w' = transport! (W P) (subst-lf-coh c (κ true) l) (δ p)

    --   κ' : (n : node P w') → W (P // (F X)) (node-type P w' n)
    --   κ' n = transport (W (P // (F X))) (node-inv-coh P (δ p) (subst-lf-coh c (κ true) l) n) (κ (inr (p , n'))) 

    --     where n' : node P (δ p)
    --           n' = <– (node-inv P (δ p) (subst-lf-coh c (κ true) l)) n

    -- subst-lcl (lf i) κ = lf i
    -- subst-lcl (nd i (c , δ)) κ = graft P i (subst c (κ (inl unit))) (λ l → subst-lcl (w' l) (κ' l))
    --   where open SubstLcl c δ κ 


    -- subst-lf-coh c (lf .(_ , c)) (p , unit) = idp
    -- subst-lf-coh c (nd .(_ , c) ((w , f , x) , κ)) l =
    --   subst-lcl-lf-coh w κ l ∙ frm-coh f (–> (subst-lcl-lf-eqv w κ) l)

    -- subst-lcl-lf-eqv (lf i) κ = ide ⊤
    -- subst-lcl-lf-eqv (nd i (c , δ)) κ = 
    --   Σ-emap-l (leaf P ∘ δ) (subst-lf-eqv c (κ true)) ∘e                         -- Equivalence on base
    --   Σ-emap-r (λ l → (leaf-inv-! P (δ (p l)) (subst-lf-coh c (κ true) l))⁻¹ ∘e  -- Equivalence by transport ...
    --     subst-lcl-lf-eqv (w' l) (κ' l)) ∘e                                       -- ... and Induction Hypothesis
    --   (graft-lf-eqv P i (subst c (κ true)) (λ l → subst-lcl (w' l) (κ' l)))⁻¹    -- Characterization of graft leaves
      
    --   where open SubstLcl c δ κ

    -- subst-lcl-lf-coh (lf i) κ unit = idp
    -- subst-lcl-lf-coh (nd i (c , δ)) κ l = {!!}

