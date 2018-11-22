{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import WPaths
open import Substitution
open import PolyMonad

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

    μ-bin-frm-to : {i : I} (w : W P i) (j : I)
      → Leaf P w j
      → Param P (μ-bin w) j
    μ-bin-frm-to (lf i) j l = –> (η-frm i j) l
    μ-bin-frm-to (nd (f , ϕ)) j (k , p , l) =
      let ψ' j p = μ-bin (ϕ j p)
      in –> (γ-frm f ψ' j) (k , p , μ-bin-frm-to (ϕ k p) j l)

    μ-bin-frm-from : {i : I} (w : W P i) (j : I)
      → Param P (μ-bin w) j
      → Leaf P w j
    μ-bin-frm-from (lf i) j p = <– (η-frm i j) p
    μ-bin-frm-from (nd (f , ϕ)) j p = 
      let ψ' j p = μ-bin (ϕ j p)
          (k , p , q) = <– (γ-frm f ψ' j) p
      in k , p , μ-bin-frm-from (ϕ k p) j q
      
    postulate

      μ-bin-frm-to-from : {i : I} (w : W P i) (j : I)
        → (p : Param P (μ-bin w) j)
        → μ-bin-frm-to w j (μ-bin-frm-from w j p) == p

      μ-bin-frm-from-to : {i : I} (w : W P i) (j : I)
        → (l : Leaf P w j)
        → μ-bin-frm-from w j (μ-bin-frm-to w j l) == l

    -- Shows the above can be written as a composition ...
    -- μ-bin-frm : {i : I} (w : W P i) → Frame P w (μ-bin w)
    -- μ-bin-frm (lf i) = η-frm i
    -- μ-bin-frm (nd (f , ϕ)) j = (γ-frm f (λ j p → μ-bin (ϕ j p)) j) ∘e
    --   Σ-emap-r (λ k → Σ-emap-r (λ p → μ-bin-frm (ϕ k p) j))

    μ-bin-frm : {i : I} (w : W P i) → Frame P w (μ-bin w)
    μ-bin-frm w j = equiv (μ-bin-frm-to w j) (μ-bin-frm-from w j)
      (μ-bin-frm-to-from w j) (μ-bin-frm-from-to w j)

    BinMgm : PolyMagma P
    μ BinMgm = μ-bin
    μ-frm BinMgm = μ-bin-frm

    module _ (L : BinaryLaws P B) where

      private
        R = ⟪ BinMgm ⟫ 

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
        
      μ-graft-inv (nd (f , ϕ)) ψ = 
        let ih j p = μ-graft-inv (ϕ j p) (λ k l → ψ k (j , p , l))
            ϕ' j p = μ-bin (ϕ j p)
            ψ' j p k q = μ-bin (ψ k (j , p , <– (μ-bin-frm (ϕ j p) k) q))
        in γ f (λ j p → μ-bin (graft P (ϕ j p) (λ k l → ψ k (j , p , l))))
             =⟨ ap (γ f) (λ= (λ j → λ= (λ p → ih j p ))) ⟩
           γ f (λ j p → γ (μ-bin (ϕ j p)) (λ k q → μ-bin (ψ k (j , p , <– (μ-bin-frm (ϕ j p) k) q))))
             =⟨ assoc f ϕ' ψ' ⟩
           γ (γ f (λ j p → μ-bin (ϕ j p))) (λ j p → μ-bin (ψ j (<– (μ-bin-frm (nd (f , ϕ)) j) p))) ∎

      -- μ-graft-lf-inv : {i : I} (w : W P i)
      --   → (ψ : ∀ j → Leaf P w j → W P j)
      --   → (j : I) (l : Leaf P (graft P w ψ) j)
      --   → –> (μ-bin-frm (graft P w ψ) j) l ==
      --     –> (γ-frm (μ-bin w) (λ k p → μ-bin (ψ k (<– (μ-bin-frm w k) p))) j) {!!}
      --       [ (λ x → Param P x j) ↓ μ-graft-inv w ψ ]
      -- μ-graft-lf-inv = {!!}

      --
      --  2-level substitution invariance
      --

      μ-subst-invar : {i : I} (w : W P i)
        → (κ : (g : Ops P) → Node P w g → Op (P // R) g)
        → μ-bin (subst P w (λ g n → fst (κ g n))) == μ-bin w

      μ-subst-inv-lem : {i : I} (f : Op P i) (ϕ : Decor P f (W P))
        → (w : Op (P // R) (i , f))
        → (κ : (g : Ops P) → Node P (nd (f , ϕ)) g → Op (P // R) g)
        → μ-bin (graft P (fst (fst w))
                  (λ j l → subst P (ϕ j (–> (snd (fst w) j) l))
                  (λ g n → fst (κ g (inr (j , –> (snd (fst w) j) l , n)))))) ==
          γ f (λ j p → μ-bin (ϕ j p))

      μ-subst-invar (lf i) κ = idp
      μ-subst-invar (nd (f , ϕ)) κ =
        μ-subst-inv-lem f ϕ (κ (_ , f) (inl idp)) κ

      μ-subst-inv-lem ._ ϕ ((w , ._) , idp) κ = 
        let κp j p g n = κ g (inr (j , p , n))
            ψp j p = subst P (ϕ j p) (λ g n → fst (κp j p g n))
            ψ j l = ψp j (–> (μ-bin-frm w j) l)
            ih j p = ap (λ x → μ-bin (ψp j x)) (<–-inv-r (μ-bin-frm w j) p) ∙ μ-subst-invar (ϕ j p) (κp j p)
        in μ-bin (graft P w ψ) 
             =⟨ μ-graft-inv w ψ ⟩
           γ (μ-bin w) (λ j p → μ-bin (ψp j (–> (μ-bin-frm w j) (<– (μ-bin-frm w j) p))))
             =⟨ λ= (λ j → λ= (λ p → ih j p)) |in-ctx (λ x → γ (μ-bin w) x) ⟩ 
           γ (μ-bin w) (λ j p → μ-bin (ϕ j p)) ∎

      postulate
      
        μ-lf-invar : {i : I} (w : W P i)
          → (κ : (g : Ops P) → Node P w g → Op (P // R) g)
          → (j : I) (l : Leaf P (subst P w (λ g n → fst (κ g n))) j)
          → –> (μ-bin-frm (subst P w (λ g n → fst (κ g n))) j) l  == 
            –> (μ-bin-frm w j ∘e subst-lf-eqv P w (λ g n → fst (κ g n)) j) l
              [ (λ x → Param P x j) ↓ μ-subst-invar w κ ]
      -- μ-lf-invar (lf i) κ j l = idp
      -- μ-lf-invar (nd (f , ϕ)) κ j l = {!!}

      -- module _ {i : I} (f : Op P i) (ϕ : Decor P f (W P))
      --   (w : Op (P // R) (i , f))
      --   (κ : (g : Ops P) → Node P (nd (f , ϕ)) g → Op (P // R) g) where

      --   w' = fst (fst w)
      --   α' = snd (fst w)

      --   κ'' : (j : I) (l : Leaf P w' j) (g : Ops P) → Node P (ϕ j (–> (α' j) l)) g → InFrame P g
      --   κ'' j l g n = fst (κ g (inr (j , –> (snd (fst w) j) l , n)))
        
      --   ψ' : Decor (Fr P) w' (W P)
      --   ψ' j l = subst P (ϕ j (–> (α' j) l)) (κ'' j l)

      --   grft : W P i
      --   grft = graft P w' ψ'

      -- μ-subst-lf-inv-lem₀ : {i : I} (f : Op P i) (ϕ : Decor P f (W P))
      --   → (w : Op (P // R) (i , f))
      --   → (κ : (g : Ops P) → Node P (nd (f , ϕ)) g → Op (P // R) g)
      --   → (j : I) (l :  Leaf P (grft f ϕ w κ) j)
      --   → Type ℓ
      -- μ-subst-lf-inv-lem₀ = {!!}

      -- μ-subst-lf-inv-lem : {i : I} (f : Op P i) (ϕ : Decor P f (W P))
      --   → (w : Op (P // R) (i , f))
      --   → (κ : (g : Ops P) → Node P (nd (f , ϕ)) g → Op (P // R) g)
      --   → (j : I) (l :  Leaf P (grft f ϕ w κ) j)
      --   → –> (μ-bin-frm (grft f ϕ w κ) j) l ==
      --     –> (γ-frm f (λ k p → μ-bin (ϕ k p)) j) (graft-leaf-rec P (fst (fst w)) (λ j l → subst P (ϕ j (–> (snd (fst w) j) l))
      --             (λ g n → fst (κ g (inr (j , –> (snd (fst w) j) l , n))))) j
      --             (λ k l₀ l₁ → k , (–> (snd (fst w) k) l₀) ,
      --             (–> (μ-bin-frm (ϕ k (–> (snd (fst w) k) l₀)) j)
      --             (subst-lf-to P (ϕ k (–> (snd (fst w) k) l₀)) (λ g n → fst (κ g (inr (k , (–> (snd (fst w) k) l₀) , n)))) j l₁))) l) [ (λ x → Param P x j) ↓ μ-subst-inv-lem f ϕ w κ ]
                  
      -- μ-subst-lf-inv-lem ._ ϕ ((w , ._) , idp) κ j l = {!!}

      -- subst-lf-to : {i : I} (w : W P i)
      --   → (κ : (g : Ops P) → Node P w g → InFrame P g)
      --   → (j : I) → Leaf P (subst w κ) j → Leaf P w j
      -- subst-lf-to (lf i) κ j l = l
      -- subst-lf-to (nd (f , ϕ)) κ j = 
      --   let (w , α) = κ (_ , f) (inl idp)
      --       κ' j l g n = κ g (inr (j , –> (α j) l , n))
      --       ψ j l = subst (ϕ j (–> (α j) l)) (κ' j l)
      --   in graft-leaf-rec P w ψ j (λ k l₀ l₁ →
      --        k , –> (α k) l₀ , subst-lf-to (ϕ k (–> (α k) l₀)) (κ' k l₀) j l₁) 


      --
      --  Full substitution invariance
      --

      μ-laws : {i : I} {f : Op P i} (pd : W (P // R) (i , f))
        → μ-bin (flatn R pd) == f
        
      μ-laws-frm : {f : Ops P} (pd : W (P // R) f)
        → μ-bin-frm (flatn R pd) == flatn-frm R pd [ Frame P (flatn R pd) ↓ μ-laws pd ]

      μ-invar : SubInvar R
      μ-invar pd = pair= (μ-laws pd) (μ-laws-frm pd)

      μ-laws (lf (i , f)) = unit-l f
      μ-laws (nd (((w , ._) , idp) , κ)) =
        let κ' g n = (flatn R (κ g n) , flatn-frm R (κ g n)) , μ-invar (κ g n)
        in μ-subst-invar w κ'

      μ-laws-frm (lf (i , f)) = ↓-Op-Frame-in P (unit-l f) lem
      
        where lem : (j : I) (l : Leaf P (corolla P f) j)
                → –> (μ-bin-frm (corolla P f) j) l ==
                  –> (corolla-frm P f j) l [ (λ x → Param P x j) ↓ unit-l f ]
              lem j (j , p , idp) = unit-l-frm f j p

      μ-laws-frm (nd (((w , ._) , idp) , κ)) =
        ↓-Op-Frame-in P (μ-subst-invar w κ')
                        (μ-lf-invar w κ')

        where κ' : (g : Ops P) (n : Node P w g) → Σ (InFrame P g) (R g)
              κ' g n = (flatn R (κ g n) , flatn-frm R (κ g n)) , μ-invar (κ g n)

