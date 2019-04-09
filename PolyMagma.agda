{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial

-- Polynomial Magmas and Slicing
module PolyMagma where

  record PolyMagma {ℓ} {I : Type ℓ} (P : Poly I) : Type ℓ where
    constructor mgm
    field
      μ : {i : I} (w : W P i) → Op P i
      μ-frm : {i : I} (w : W P i) → Frame P w (μ w)

  open PolyMagma public

  -- The relation induced by a magma
  ⟪_⟫ : ∀ {ℓ} {I : Type ℓ} {P : Poly I} (M : PolyMagma P) → PolyRel P
  ⟪_⟫ {P = P} M (i , f) (w , α) = Path {A = OutFrame P w}
    (μ M w , μ-frm M w) (f , α)

  -- A biased version
  record BiasedMgm {ℓ} {I : Type ℓ} (P : Poly I) : Type ℓ where
    field

      η : (i : I) → Op P i
      η-frm : (i : I) (j : I) → (i == j) ≃ Param P (η i) j 

      γ : {i : I} (f : Op P i) (ϕ : (j : I) → Param P f j → Op P j) → Op P i
      γ-frm : {i : I} (f : Op P i) (ϕ : (j : I) → Param P f j → Op P j)
        → (j : I) → Σ I (λ k → Σ (Param P f k) (λ p → Param P (ϕ k p) j)) ≃ Param P (γ f ϕ) j 

  --
  --  Helper functions and path-over principles
  --

  module _ {ℓ} {I : Type ℓ} {P : Poly I} (B : BiasedMgm P) where

    open BiasedMgm B

    γ-frm-to : {i j : I} {f : Op P i} {ϕ : (j : I) → Param P f j → Op P j}
      → Σ I (λ k → Σ (Param P f k) (λ p → Param P (ϕ k p) j)) → Param P (γ f ϕ) j 
    γ-frm-to kpq = –> (γ-frm _ _ _) kpq

    γ-frm-from : {i j : I} {f : Op P i} {ϕ : (j : I) → Param P f j → Op P j}
      → Param P (γ f ϕ) j → Σ I (λ k → Σ (Param P f k) (λ p → Param P (ϕ k p) j))
    γ-frm-from p = <– (γ-frm _ _ _) p 
    
    γ-frm-srt : {i j : I} {f : Op P i} {ϕ : (j : I) → Param P f j → Op P j}
      → Param P (γ f ϕ) j → I
    γ-frm-srt p = fst (<– (γ-frm _ _ _) p)

    γ-frm-fst-param : {i j : I} {f : Op P i} {ϕ : (j : I) → Param P f j → Op P j}
      → (p : Param P (γ f ϕ) j) → Param P f (γ-frm-srt p)
    γ-frm-fst-param p = fst (snd (<– (γ-frm _ _ _) p))

    γ-frm-snd-param : {i j : I} {f : Op P i} {ϕ : (j : I) → Param P f j → Op P j}
      → (p : Param P (γ f ϕ) j) → Param P (ϕ (γ-frm-srt p) (γ-frm-fst-param p)) j
    γ-frm-snd-param p = snd (snd (<– (γ-frm _ _ _) p))

    -- Here are some path over principles
    ↓-γ-param : {i j : I} {f : Op P i}
      → {ϕ₀ ϕ₁ : Decor P f (Op P)}
      → (r : ϕ₀ == ϕ₁)
      → {k : I} {p : Param P f k}
      → {q₀ : Param P (ϕ₀ k p) j} {q₁ : Param P (ϕ₁ k p) j}
      → (c : q₀ == q₁ [ (λ x → Param P x j) ↓ app= (app= r k) p ])
      → –> (γ-frm f ϕ₀ j) (k , p , q₀) ==
        –> (γ-frm f ϕ₁ j) (k , p , q₁)
          [ (λ x → Param P x j) ↓ ap (γ f) r ]
    ↓-γ-param idp idp = idp

    -- This is now a simple consequence of the previous...
    ↓-γ-param' : {i j : I} {f : Op P i}
      → {ϕ₀ ϕ₁ : Decor P f (Op P)}
      → {ψ : (j : I) (p : Param P f j) → ϕ₀ j p == ϕ₁ j p}
      → {k : I} {p : Param P f k}
      → {q₀ : Param P (ϕ₀ k p) j} {q₁ : Param P (ϕ₁ k p) j}
      → (c : q₀ == q₁ [ (λ x → Param P x j) ↓ ψ k p ])
      → –> (γ-frm f ϕ₀ j) (k , p , q₀) ==
        –> (γ-frm f ϕ₁ j) (k , p , q₁)
          [ (λ x → Param P x j) ↓ ap (γ f) (Decor-== P ψ) ]
    ↓-γ-param' {ψ = ψ} {k} {p} {q₀} {q₁} c =
      ↓-γ-param (Decor-== P ψ)
        (transport (λ y → q₀ == q₁ [ (λ x → Param P x _) ↓ y ])
                   (Decor-==-β P ψ k p) c)

    --
    --  Constructing a PolyMagma from a biased one
    --
    
    μ-bsd : {i : I} → W P i → Op P i
    μ-bsd (lf i) = η i
    μ-bsd (nd (f , ϕ)) = γ f (λ j p → μ-bsd (ϕ j p))

    μ-bsd-frm-to : {i : I} (w : W P i) (j : I)
      → Leaf P w j
      → Param P (μ-bsd w) j
    μ-bsd-frm-to (lf i) j l = –> (η-frm i j) l
    μ-bsd-frm-to (nd (f , ϕ)) j (k , p , l) =
      let ϕ' j p = μ-bsd (ϕ j p)
      in –> (γ-frm f ϕ' j) (k , p , μ-bsd-frm-to (ϕ k p) j l)

    μ-bsd-frm-from : {i : I} (w : W P i) (j : I)
      → Param P (μ-bsd w) j
      → Leaf P w j
    μ-bsd-frm-from (lf i) j p = <– (η-frm i j) p
    μ-bsd-frm-from (nd (f , ϕ)) j p₀ = 
      let ϕ' j p = μ-bsd (ϕ j p)
          (k , p , q) = <– (γ-frm f ϕ' j) p₀
      in k , p , μ-bsd-frm-from (ϕ k p) j q
      
    μ-bsd-frm-to-from : {i : I} (w : W P i) (j : I)
      → (p : Param P (μ-bsd w) j)
      → μ-bsd-frm-to w j (μ-bsd-frm-from w j p) == p
    μ-bsd-frm-to-from (lf i) j p = <–-inv-r (η-frm i j) p
    μ-bsd-frm-to-from (nd (f , ϕ)) j p₀ = 
      let ϕ' j p = μ-bsd (ϕ j p)
          (k , p , q) = <– (γ-frm f ϕ' j) p₀
      in ap (λ x → –> (γ-frm f ϕ' j) (k , p , x)) (μ-bsd-frm-to-from (ϕ k p) j q) ∙
         <–-inv-r (γ-frm f ϕ' j) p₀

    μ-bsd-frm-from-to : {i : I} (w : W P i) (j : I)
      → (l : Leaf P w j)
      → μ-bsd-frm-from w j (μ-bsd-frm-to w j l) == l
    μ-bsd-frm-from-to (lf i) j l = <–-inv-l (η-frm i j) l
    μ-bsd-frm-from-to (nd (f , ϕ)) j (k , p , l) =
      let ϕ' j p = μ-bsd (ϕ j p)
      in ap (λ x → (fst x , fst (snd x) , μ-bsd-frm-from (ϕ (fst x) (fst (snd x))) j (snd (snd x))))
            (<–-inv-l (γ-frm f ϕ' j) (k , p , μ-bsd-frm-to (ϕ k p) j l)) ∙
         ap (λ x → (k , p , x)) (μ-bsd-frm-from-to (ϕ k p) j l)

    μ-bsd-frm : {i : I} (w : W P i) → Frame P w (μ-bsd w)
    μ-bsd-frm w j = equiv (μ-bsd-frm-to w j) (μ-bsd-frm-from w j)
      (μ-bsd-frm-to-from w j) (μ-bsd-frm-from-to w j)

    BsdMgm : PolyMagma P
    μ BsdMgm = μ-bsd
    μ-frm BsdMgm = μ-bsd-frm
