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
        → (j : I) → Σ I (λ k → Σ (Param P f k) (λ p → Param P (ϕ k p) j)) ≃ Param P (γ f ϕ) j 

  record BinaryLaws {ℓ} {I : Type ℓ} (P : Poly I) (B : BinaryOp P) : Type ℓ where

    open BinaryOp B

    field

      unit-l : {i : I} (f : Op P i) → γ f (λ j _ → η j) == f
      unit-l-frm : {i : I} (f : Op P i) (j : I) (p : Param P f j)
        → –> (γ-frm f (λ j p → η j) j) (j , p , –> (η-frm j j) idp) == p [ (λ x → Param P x j) ↓ unit-l f ]

      -- Exactly.  And we'll need a coherence for each of the other two
      -- which does the same thing, allowing us to reconstruct the action
      -- on of the frames on their multipled composites.

      unit-r : {i : I} (f : Op P i) → f == γ (η i) (λ j p → transport (Op P) (<– (η-frm i j) p) f) 
      unit-r-frm : (i : I) (f : Op P i) (j : I) (p : Param P f j)
        → p == –> (γ-frm (η i) (λ j p → transport (Op P) (<– (η-frm i j) p) f) j)
                  (i , –> (η-frm i i) idp , transport! (λ x → Param P (transport (Op P) x f) j) (<–-inv-l (η-frm i i) idp) p )
             [ (λ x → Param P x j) ↓ unit-r f ]

      assoc : {i : I} (f : Op P i)
        → (ϕ : (j : I) → Param P f j → Op P j)
        → (ψ : (j : I) (p : Param P f j) (k : I) → Param P (ϕ j p) k → Op P k)
        → γ f (λ j p → γ (ϕ j p) (λ k q → ψ j p k q)) == 
          γ (γ f ϕ) (λ j p → let (k , p₀ , p₁) = <– (γ-frm f ϕ j) p in ψ k p₀ j p₁ ) 
          

  module _ {ℓ} {I : Type ℓ} (P : Poly I) (B : BinaryOp P) where

    open BinaryOp B

    μ-bin : {i : I} → W P i → Op P i
    μ-bin (lf i) = η i
    μ-bin (nd (f , ϕ)) = γ f (λ j p → μ-bin (ϕ j p))

    -- Probably the same computational issues here...
    μ-bin-frm : {i : I} (w : W P i) → Frame P w (μ-bin w)
    μ-bin-frm (lf i) = η-frm i
    μ-bin-frm (nd (f , ϕ)) j = (γ-frm f (λ j p → μ-bin (ϕ j p)) j) ∘e
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
      μ-graft-inv (lf i) ψ = unit-r (μ-bin (ψ i idp)) ∙
        ap (γ (η i)) (λ= (λ j → λ= (λ p → lem (<– (η-frm i j) p))))
    
        where lem : {j : I} (q : i == j)
                → transport (Op P) q (μ-bin (ψ i idp)) ==
                  μ-bin (ψ j q)
              lem idp = idp
        
      μ-graft-inv (nd (f , ϕ)) ψ = {!assoc f (λ j p → μ-bin (ϕ j p))!}

      -- substitution invariance at level 2 now follows easily ...
      -- (could reorganize a bit to make it cleaner: combine the
      --  last two steps into a single in context with the induction
      --  hyp and cancellation as a separate lemma ...)
      μ-subst-invar : {i : I} (w : W P i)
        → (κ : (g : Ops P) → Node P w g → Op (P // BinMgm) g)
        → μ-bin (subst P w (λ g n → to-subst BinMgm (κ g n))) == μ-bin w
      μ-subst-invar (lf i) κ = idp
      μ-subst-invar (nd (f , ϕ)) κ with κ (_ , f) (inl idp)
      μ-subst-invar (nd (._ , ϕ)) κ | (w , idp) =
        let κp j p g n = to-subst BinMgm (κ g (inr (j , p , n)))
            ψp j p = subst P (ϕ j p) (κp j p)
            ψ j l = ψp j (–> (μ-bin-frm w j) l)
        in μ-bin (graft P w ψ)
             =⟨ μ-graft-inv w ψ ⟩
           γ (μ-bin w) (λ j p → μ-bin (ψp j (–> (μ-bin-frm w j) (<– (μ-bin-frm w j) p))))
             =⟨ ap (γ (μ-bin w)) (λ= (λ j → λ= (λ p → ap (λ x → μ-bin (subst P (ϕ j x)
               (λ g n → to-subst BinMgm (κ g (inr (j , x , n)))))) (<–-inv-r (μ-bin-frm w j) p)))) ⟩ 
           γ (μ-bin w) (λ j p → μ-bin (ψp j p))
             =⟨ ap (γ (μ-bin w)) (λ= (λ j → λ= (λ p → μ-subst-invar (ϕ j p) (λ g n → κ g (inr (j , p , n)))))) ⟩ 
           γ (μ-bin w) (λ j p → μ-bin (ϕ j p)) ∎

      -- A bit more complicated than I thought, but okay ...
      μ-subst-invar-frm : {i : I} (w : W P i)
        → (κ : (g : Ops P) → Node P w g → Op (P // BinMgm) g)
        → (j : I) (l : Leaf P w j)
        → –> (μ-bin-frm (subst P w (λ g n → to-subst BinMgm (κ g n))) j)
               (<– (subst-lf-eqv P w (λ g n → to-subst BinMgm (κ g n)) j) l) ==
          –> (μ-bin-frm w j) l [ (λ x → Param P x j) ↓ μ-subst-invar w κ ]
      μ-subst-invar-frm = {!!}
      
      -- Abbreviations ...
      sf = slc-flatn BinMgm
      sff = slc-flatn-frm BinMgm

      μ-laws : {i : I} {f : Op P i} (pd : W (P // BinMgm) (i , f))
        → μ-bin (sf pd) == f

      μ-laws-frm : {f : Ops P} (pd : W (P // BinMgm) f)
        → μ-bin-frm (sf pd) == sff pd [ Frame P (sf pd) ↓ μ-laws pd ]

      μ-laws (lf (i , f)) = unit-l f
      μ-laws (nd ((w , idp) , κ)) =
        let ih g n = μ-laws-frm (κ g n)
            r = ap (λ x → μ-bin (subst P w x)) (λ= (λ g → (λ= (λ n → pair= idp (! (to-transp (ih g n)))))))
            s = μ-subst-invar w (λ g n → sf (κ g n) , μ-laws (κ g n))
        in r ∙ s

      μ-laws-frm (lf (i , f)) = ↓-Op-Frame-in P (unit-l f) lem
      
        where lem : (j : I) (l : Leaf P (corolla P f) j)
                → –> (μ-bin-frm (corolla P f) j) l ==
                  –> (corolla-frm P f j) l [ (λ x → Param P x j) ↓ unit-l f ]
              lem j (j , p , idp) = unit-l-frm f j p

      μ-laws-frm (nd ((w , idp) , κ)) = 
        let ih g n = μ-laws-frm (κ g n)
            r = ap (λ x → μ-bin (subst P w x)) (λ= (λ g → (λ= (λ n → pair= idp (! (to-transp (ih g n)))))))
        in {!r!}

          where s : μ-bin (subst P w (λ g n → to-subst BinMgm (sf (κ g n) , μ-laws (κ g n)))) == μ-bin w
                s = μ-subst-invar w (λ g n → sf (κ g n) , μ-laws (κ g n))



      -- Just a renaming ...
      μ-coh-wit : CohWit BinMgm
      μ-coh-wit = μ-laws


