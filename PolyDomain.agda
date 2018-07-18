{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Poly

module PolyDomain where

  Frame : {I : Type₀} (P : Poly I) {i : I} (w : W P i) (c : γ P i) → Type₀
  Frame {I} P w c = (j : I) → Leaf P w j ≃ ρ P c j

  FillingFamily : {I : Type₀} → Poly I → Type₁
  FillingFamily {I} P = {i : I} {w : W P i} {c : γ P i} → Frame P w c → Type₀

  _//_ : {I : Type₀} (P : Poly I) (F : FillingFamily P) → Poly (Σ I (γ P))
  γ (P // F) (i , c) = Σ (W P i) (λ w → Σ (Frame P w c) F)
  ρ (P // F) (w , f , x) (j , d) = Node P w d

  --
  --  The Baez-Dolan substitution operation
  --

  module Substitution {I : Type₀} {P : Poly I} (F : FillingFamily P) where

    {-# TERMINATING #-}
    flatten : {i : I} (c : γ P i)
      → (tr : W (P // F) (i , c))
      → W P i

    -- The flattened tree has a canonical c-frame
    flatten-frm : {i : I} (c : γ P i)
      → (tr : W (P // F) (i , c))
      → (j : I) → Leaf P (flatten c tr) j ≃ ρ P c j

    substitute : {i : I} (w : W P i)
      → (κ : (c : Σ I (γ P)) → Node P w (snd c) → W (P // F) c)
      → W P i

    -- A substituted tree has the same leaves
    substitute-lf-eqv : {i : I} (w : W P i)
      → (κ : (c : Σ I (γ P)) → Node P w (snd c) → W (P // F) c)
      → (j : I) → Leaf P (substitute w κ) j ≃ Leaf P w j

    flatten c (lf .(_ , c)) = corolla P c
    flatten c (nd ((w , f , x) , ε)) = substitute w ε

    flatten-frm c (lf .(_ , c)) j = corolla-lf-eqv P c j
    flatten-frm c (nd ((w , f , x) , ε)) j = f j ∘e substitute-lf-eqv w ε j

    substitute (lf i) κ = lf i
    substitute (nd {i} (c , δ)) κ =
      let tr = κ (i , c) (this c δ)
          p j l = –> (flatten-frm c tr j) l
          ε j l = substitute (δ j (p j l)) (λ ic n → κ ic (that c δ (p j l) n))
      in graft P (flatten c tr) ε 

    substitute-lf-eqv (lf i) κ j = ide (Leaf P (lf i) j)
    substitute-lf-eqv (nd {i} (c , δ)) κ j =
      let tr = κ (i , c) (this c δ)
          p j l = –> (flatten-frm c tr j) l
          κ' j l ic n = κ ic (that c δ (p j l) n)
          ε j l = substitute (δ j (p j l)) (κ' j l) 
      in nd-lf-eqv P c δ j ∘e
         Σ-emap-r (λ k → Σ-emap-l (λ p → Leaf P (δ k p) j) (flatten-frm c tr k) ∘e
                         Σ-emap-r (λ l → substitute-lf-eqv (δ k (p k l)) (κ' k l) j)) ∘e
         graft-leaf-eqv P (flatten c tr) ε j

  --
  --  Polynomial Domains
  --
  
  record PolyDomain {I : Type₀} (P : Poly I) : Type₁ where
    coinductive
    field

      F : {i : I} {w : W P i} {c : γ P i} → Frame P w c → Type₀
      H : PolyDomain (P // F)

  open PolyDomain public

