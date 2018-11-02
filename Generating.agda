{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import WPaths
open import Substitution
open import PolyMonad
open import TreeLemmas

module Generating where

  record BinaryOp {ℓ} {I : Type ℓ} (P : Poly I) : Type ℓ where
    field

      η : (i : I) → Op P i
      η-frm : (i : I) (j : I) → (i == j) ≃ Param P (η i) j 

      γ : {i : I} (f : Op P i) (ϕ : (j : I) → Param P f j → Op P j) → Op P i
      γ-frm : {i : I} (f : Op P i) (ϕ : (j : I) → Param P f j → Op P j)
        → (j : I) → Param P (γ f ϕ) j ≃ Σ I (λ k → Σ (Param P f k) (λ p → Param P (ϕ k p) j))

  record BinaryLaws {ℓ} {I : Type ℓ} (P : Poly I) (B : BinaryOp P) : Type ℓ where

    open BinaryOp B

    field

      unit-l : {i : I} (f : Op P i) → γ f (λ j _ → η j) == f
      unit-r : (i : I) (f : Op P i) → f == γ (η i) (λ j p → transport (Op P) (<– (η-frm i j) p) f) 

      assoc : {i : I} (f : Op P i)
        → (ϕ : (j : I) → Param P f j → Op P j)
        → (ψ : (j : I) (p : Param P f j) (k : I) → Param P (ϕ j p) k → Op P k)
        → γ f (λ j p → γ (ϕ j p) (λ k q → ψ j p k q)) == 
          γ (γ f ϕ) (λ j p → let (k , p₀ , p₁) = –> (γ-frm f ϕ j) p in ψ k p₀ j p₁ ) 
          

  module _ {ℓ} {I : Type ℓ} (P : Poly I) (B : BinaryOp P) where

    open BinaryOp B

    μ-bin : {i : I} → W P i → Op P i
    μ-bin (lf i) = η i
    μ-bin (nd (f , ϕ)) = γ f (λ j p → μ-bin (ϕ j p))

    -- Probably the same computational issues here...
    μ-bin-frm : {i : I} (w : W P i) → Frame P w (μ-bin w)
    μ-bin-frm (lf i) = η-frm i
    μ-bin-frm (nd (f , ϕ)) j = (γ-frm f (λ j p → μ-bin (ϕ j p)) j)⁻¹ ∘e
      Σ-emap-r (λ k → Σ-emap-r (λ p → μ-bin-frm (ϕ k p) j))
    
    BinMgm : PolyMagma P
    μ BinMgm = μ-bin
    μ-frm BinMgm = μ-bin-frm

    module _ (L : BinaryLaws P B) where

      open BinaryLaws L

      μ-graft-inv : {i : I} (w : W P i)
        → (ψ : ∀ j → Leaf P w j → W P j)
        → μ-bin (graft P w ψ) ==
          γ (μ-bin w) (λ j p → μ-bin (ψ j (<– (μ-bin-frm w j) p)))
      μ-graft-inv (lf i) ψ = unit-r i (μ-bin (ψ i idp)) ∙
        ap (γ (η i)) (λ= (λ j → λ= (λ p → {!!})))
      μ-graft-inv (nd (f , ϕ)) ψ = {!assoc f (λ j p → μ-bin (ϕ j p))!}

      sf = slc-flatn P BinMgm
      sff = slc-flatn-frm P BinMgm

      μ-subst-inv : {i : I} (w : W P i)
        → (κ : (j : Σ I (Op P)) → Node P w j → W (P // BinMgm) j) →
          μ-bin (subst P w (λ g n → sf (κ g n) , sff (κ g n))) ==
          μ-bin w
      μ-subst-inv (lf i) κ = idp
      μ-subst-inv (nd (f , ϕ)) κ = 
        let pd = κ (_ , f) (inl idp)
            p j l = –> (sff pd j) l
            κ' j l g n = κ g (inr (j , p j l , n))
            ψ j l = subst P (ϕ j (p j l)) (λ g n → sf (κ' j l g n) , sff (κ' j l g n))
        in μ-bin (graft P (sf pd) ψ)
             =⟨ μ-graft-inv (sf pd) ψ ⟩
           γ (μ-bin (sf pd)) (λ j q → μ-bin (ψ j (<– (μ-bin-frm (sf pd) j) q)))
             =⟨ {!!} ⟩ 
           γ f (λ j p → μ-bin (ϕ j p)) ∎

      μ-laws : {i : I} {f : Op P i} (pd : W (P // BinMgm) (i , f))
        → μ-bin (sf pd) == f
      μ-laws (lf (i , f)) = unit-l f
      μ-laws {i} .{μ-bin w} (nd ((w , idp) , κ)) =
        μ-subst-inv w κ

      -- Just a renaming ...
      μ-coh-wit : CohWit P BinMgm
      μ-coh-wit = μ-laws


