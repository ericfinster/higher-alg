{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Grafting
open import Substitution
open import PolyMonad
open import WPaths

module Biased where

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
  --  Laws for a Biased Magma
  --

  record BiasedLaws {ℓ} {I : Type ℓ} (P : Poly I) (B : BiasedMgm P) : Type ℓ where

    open BiasedMgm B

    field

      unit-l : {i : I} (f : Op P i) → γ f (λ j _ → η j) == f
      unit-r : {i : I} (ϕ : (j : I) → Param P (η i) j → Op P j)
        → ϕ i (–> (η-frm i i) idp) == γ (η i) ϕ
      assoc : {i : I} (f : Op P i)
        → (ϕ : (j : I) → Param P f j → Op P j)
        → (ψ : (j : I) → Σ I (λ k → Σ (Param P f k) (λ p → Param P (ϕ k p) j)) → Op P j)
        → γ f (λ j p → γ (ϕ j p) (λ k q → ψ k (j , p , q))) ==
          γ (γ f ϕ) (λ j p → ψ j (<– (γ-frm f ϕ j) p))

      unit-l-frm : {i : I} (f : Op P i) (j : I) (p : Param P f j)
        → γ-frm-to B (j , p , –> (η-frm j j) idp) == p [ (λ x → Param P x j) ↓ unit-l f ]

      unit-r-frm : {i : I} (ϕ : (j : I) → Param P (η i) j → Op P j) (j : I) (p : Param P (ϕ i (–> (η-frm i i) idp)) j)
        → p == γ-frm-to B (i , –> (η-frm i i) idp , p) [ (λ x → Param P x j) ↓ unit-r ϕ ]

      assoc-frm : {i : I} (f : Op P i)
        → (ϕ : (j : I) → Param P f j → Op P j)
        → (ψ : (j : I) → Σ I (λ k → Σ (Param P f k) (λ p → Param P (ϕ k p) j)) → Op P j) (l : I)
        → (j : I) (p : Param P f j) (k : I) (q : Param P (ϕ j p) k) (r : Param P (ψ k (j , p , q)) l)
        → γ-frm-to B (j , p , γ-frm-to B (k , q , r)) ==
          γ-frm-to B (k , γ-frm-to B (j , p , q) , transport! (λ x → Param P (ψ k x) l) (<–-inv-l (γ-frm f ϕ k) (j , p , q)) r)
          [ (λ x → Param P x l) ↓ assoc f ϕ ψ ]

  --
  --  Construction of the associated magma and proof of
  --  its subdivision invariance.
  --

  module _ {ℓ} {I : Type ℓ} (P : Poly I) (B : BiasedMgm P) where

    open BiasedMgm B

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

    module _ (L : BiasedLaws P B) where

      private
        R = ⟪ BsdMgm ⟫ 

      open BiasedLaws L

      μ-graft-inv : {i : I} (w : W P i)
        → (ψ : ∀ j → Leaf P w j → W P j)
        → μ-bsd (graft P w ψ) ==
          γ (μ-bsd w) (λ j p → μ-bsd (ψ j (<– (μ-bsd-frm w j) p)))
      μ-graft-inv (lf i) ψ =
        let ψ' j p = μ-bsd (ψ j (<– (μ-bsd-frm (lf i) j) p))
        in ap (λ q → μ-bsd (ψ i q)) (! (<–-inv-l (η-frm i i) idp)) ∙ unit-r ψ'  
      μ-graft-inv (nd (f , ϕ)) ψ = 
        let ih j p = μ-graft-inv (ϕ j p) (λ k l → ψ k (j , p , l))
            ϕ' j p = μ-bsd (ϕ j p)
            ψ' j kpq = let (k , p , q) = kpq in μ-bsd (ψ j (k , p , <– (μ-bsd-frm (ϕ k p) j) q))
        in ap (γ f) (Decor-== P ih) ∙ assoc f ϕ' ψ'
        -- in γ f (λ j p → μ-bsd (graft P (ϕ j p) (λ k l → ψ k (j , p , l))))
        --      =⟨ ap (γ f) (Decor-== P ih) ⟩
        --    γ f (λ j p → γ (μ-bsd (ϕ j p)) (λ k q → μ-bsd (ψ k (j , p , <– (μ-bsd-frm (ϕ j p) k) q))))
        --      =⟨ assoc f ϕ' ψ' ⟩
        --    γ (γ f (λ j p → μ-bsd (ϕ j p))) (λ j p → μ-bsd (ψ j (<– (μ-bsd-frm (nd (f , ϕ)) j) p))) ∎

      μ-graft-lf-param : {i : I} (w : W P i)
        → (ψ : ∀ j → Leaf P w j → W P j)
        → (j : I) (l : Leaf P (graft P w ψ) j)
        → Param P (γ (μ-bsd w) (λ j p → μ-bsd (ψ j (<– (μ-bsd-frm w j) p)))) j
      μ-graft-lf-param w ψ j l = 
        let (k , l₀ , l₁) = <– (graft-leaf-eqv P w ψ j) l
        in γ-frm-to B (k , –> (μ-bsd-frm w k) l₀ ,
          transport! (λ x → Param P (μ-bsd (ψ k x)) j)
                     (<–-inv-l (μ-bsd-frm w k) l₀)
                     (–> (μ-bsd-frm (ψ k l₀) j) l₁))

      μ-graft-lf-inv : {i : I} (w : W P i)
        → (ψ : ∀ j → Leaf P w j → W P j)
        → (j : I) (l : Leaf P (graft P w ψ) j)
        → –> (μ-bsd-frm (graft P w ψ) j) l == μ-graft-lf-param w ψ j l
            [ (λ x → Param P x j) ↓ μ-graft-inv w ψ ]
      μ-graft-lf-inv (lf i) ψ j l =
        let ψ' j p = μ-bsd (ψ j (<– (μ-bsd-frm (lf i) j) p))
        in ↓-ap-in (λ x → Param P x j) (λ q → μ-bsd (ψ i q))
                   (to-transp!-↓ (λ x → Param P (μ-bsd (ψ i x)) j)
                                 (<–-inv-l (μ-bsd-frm (lf i) i) idp)
                                 (–> (μ-bsd-frm (ψ i idp) j) l)) ∙ᵈ
           unit-r-frm ψ' j (transport! (λ pth → Param P (μ-bsd (ψ i pth)) j)
                                       (<–-inv-l (μ-bsd-frm (lf i) i) idp)
                                       (–> (μ-bsd-frm (ψ i idp) j) l)) 
  

      μ-graft-lf-inv (nd (f , ϕ)) ψ j (k , p , l) =
        let ih-inv j p = μ-graft-inv (ϕ j p) (λ k l → ψ k (j , p , l))
            ih = μ-graft-lf-inv (ϕ k p) (λ k' l → ψ k' (k , p , l)) j l
            ϕ' j p = μ-bsd (ϕ j p)
            ψ' j kpq = let (k , p , q) = kpq in μ-bsd (ψ j (k , p , <– (μ-bsd-frm (ϕ k p) j) q))
            (k₀ , l₀ , l₁) = <– (graft-leaf-eqv P (ϕ k p) (λ k' l' → ψ k' (k , p , l')) j) l
            p₀ = –> (μ-bsd-frm (ϕ k p) k₀) l₀
            p₁ = –> (μ-bsd-frm (ψ k₀ (k , p , l₀)) j) l₁

            pth₀ = μ-bsd-frm-from-to (ϕ k p) k₀ l₀
            pth₁ = <–-inv-l (γ-frm f ϕ' k₀) (k , p , p₀)

            Q x = Param P (μ-bsd (ψ k₀ (fst x , fst (snd x) , snd (snd x)))) j
            t x = fst x , fst (snd x) , <– (μ-bsd-frm (ϕ (fst x) (fst (snd x))) k₀) (snd (snd x))
            s x = k , p , x
            
            p₁' = transport! (Q ∘ s) pth₀ p₁

            -- With the above definitions, this is just transport based path algebra ....
            lem = transport! (Q ∘ t) pth₁  
                    (transport! (Q ∘ s) pth₀ p₁)
                    =⟨ transp!-ap Q t pth₁ p₁' ⟩ 
                  transport! Q (ap t pth₁) p₁'
                    =⟨ transp!-ap Q s pth₀ p₁ |in-ctx (λ z → transport! Q (ap t pth₁) z) ⟩ 
                  transport! Q (ap t pth₁) (transport! Q (ap s pth₀) p₁)
                    =⟨ ! (transp!-∙ Q (ap t pth₁) (ap s pth₀) p₁) ⟩
                  transport! Q (ap t pth₁ ∙ ap s pth₀) p₁ ∎ 
    
        in ↓-γ-param' B ih ∙ᵈ assoc-frm f ϕ' ψ' j k p k₀ p₀ p₁' ∙'ᵈ
             ap (λ x → γ-frm-to B (k₀ , γ-frm-to B (k , p , p₀) , x)) lem


      --
      --  2-level substitution invariance
      --

      μ-subst-invar : {i : I} (w : W P i)
        → (κ : (g : Ops P) → Node P w g → Op (P // R) g)
        → μ-bsd (subst P w (λ g n → fst (κ g n))) == μ-bsd w

      μ-subst-inv-lem : {i : I} (f : Op P i) (ϕ : Decor P f (W P))
        → (w : Op (P // R) (i , f))
        → (κ : (g : Ops P) → Node P (nd (f , ϕ)) g → Op (P // R) g)
        → μ-bsd (graft P (fst (fst w))
                  (λ j l → subst P (ϕ j (–> (snd (fst w) j) l))
                  (λ g n → fst (κ g (inr (j , –> (snd (fst w) j) l , n)))))) ==
          γ f (λ j p → μ-bsd (ϕ j p))

      μ-subst-invar (lf i) κ = idp
      μ-subst-invar (nd (f , ϕ)) κ =
        μ-subst-inv-lem f ϕ (κ (_ , f) (inl idp)) κ

      μ-subst-inv-lem ._ ϕ ((w , ._) , idp) κ = 
        let κp j p g n = κ g (inr (j , p , n))
            ψp j p = subst P (ϕ j p) (λ g n → fst (κp j p g n))
            ψ j l = ψp j (–> (μ-bsd-frm w j) l)
            ih j p = ap (λ x → μ-bsd (ψp j x)) (<–-inv-r (μ-bsd-frm w j) p) ∙ μ-subst-invar (ϕ j p) (κp j p)
         in μ-graft-inv w ψ ∙ ap (γ (μ-bsd w)) (Decor-== P ih)
        -- in μ-bsd (graft P w ψ) 
        --      =⟨ μ-graft-inv w ψ ⟩
        --    γ (μ-bsd w) (λ j p → μ-bsd (ψp j (–> (μ-bsd-frm w j) (<– (μ-bsd-frm w j) p))))
        --      =⟨ λ= (λ j → λ= (λ p → ih j p)) |in-ctx (λ x → γ (μ-bsd w) x) ⟩ 
        --    γ (μ-bsd w) (λ j p → μ-bsd (ϕ j p)) ∎


      -- Yeah, this needs some serious cleanup ...
      μ-lf-invar : {i : I} (w : W P i)
        → (κ : (g : Ops P) → Node P w g → Op (P // R) g)
        → (j : I) (l : Leaf P (subst P w (λ g n → fst (κ g n))) j)
        → –> (μ-bsd-frm (subst P w (λ g n → fst (κ g n))) j) l  == 
          –> (μ-bsd-frm w j ∘e (subst-lf-eqv P w (λ g n → fst (κ g n)) j) ⁻¹) l
            [ (λ x → Param P x j) ↓ μ-subst-invar w κ ]

      μ-subst-lf-inv-lem : {i j : I} (f : Op P i) (ϕ : Decor P f (W P))
        → (w : W P i) (α : Frame P w f) (r : R (i , f) (w , α))
        → (κ : (g : Ops P) → Node P (nd (f , ϕ)) g → Op (P // R) g)
        → (l : Leaf P (graft P w (λ j' l' → subst P (ϕ j' (–> (α j') l')) (λ g n → fst (κ g (inr (j' , (–> (α j') l') , n))) ))) j)
        → –> (μ-bsd-frm (graft P w (λ j' l' → subst P (ϕ j' (–> (α j') l')) (λ g n → fst (κ g (inr (j' , (–> (α j') l') , n))) ))) j) l ==
          (let (k , l₀ , l₁) = graft-leaf-from P w (λ j' l' → subst P (ϕ j' (–> (α j') l')) (λ g n → fst (κ g (inr (j' , –> (α j') l' , n))))) j l
            in –> (γ-frm f (λ k p → μ-bsd (ϕ k p)) j) (k , (–> (α k) l₀) ,
                 –> (μ-bsd-frm (ϕ k (–> (α k) l₀)) j) (subst-lf-from P (ϕ k (–> (α k) l₀)) (λ g n → fst (κ g (inr (k , (–> (α k) l₀) , n)))) j l₁)))
            [ (λ x → Param P x j) ↓ μ-subst-inv-lem f ϕ ((w , α) , r) κ ]

      μ-lf-invar (lf i) κ j l = idp
      μ-lf-invar (nd (f , ϕ)) κ j l =
        let ((w , α) , r) = κ (_ , f) (inl idp)
        in μ-subst-lf-inv-lem f ϕ w α r κ l 


      μ-subst-lf-inv-lem ._ ϕ w ._ idp κ l = 
        let κp j p g n = κ g (inr (j , p , n))
            ψp j p = subst P (ϕ j p) (λ g n → fst (κp j p g n))
            ψ j l = ψp j (–> (μ-bsd-frm w j) l)
            (k , l₀ , l₁) = graft-leaf-from P w ψ _ l
            p₀ = –> (μ-bsd-frm w k) l₀
            p₁ = –> (μ-bsd-frm (ψp k p₀) _) l₁
            Q x = Param P (μ-bsd (ψp k x)) _
            Q' x = Param P (μ-bsd (ψp k (–> (μ-bsd-frm w k) x))) _

            lem₀ = transport! Q' (<–-inv-l (μ-bsd-frm w k) l₀) p₁
                     =⟨ transp!-ap Q (–> (μ-bsd-frm w k)) (<–-inv-l (μ-bsd-frm w k) l₀) p₁ ⟩
                   transport! Q (ap (–> (μ-bsd-frm w k)) (<–-inv-l (μ-bsd-frm w k) l₀)) p₁
                     =⟨ <–-inv-adj (μ-bsd-frm w k) l₀ |in-ctx (λ x → transport! Q x p₁) ⟩ 
                   transport! Q (<–-inv-r (μ-bsd-frm w k) p₀) p₁ ∎

            lem : transport! Q' (<–-inv-l (μ-bsd-frm w k) l₀) p₁ == p₁ [ Q ↓ <–-inv-r (μ-bsd-frm w k) p₀ ]
            lem = lem₀ ∙ᵈ to-transp!!-↓ Q (<–-inv-r (μ-bsd-frm w k) p₀) p₁ 
            
        in μ-graft-lf-inv w ψ _ l ∙ᵈ
           ↓-γ-param' B (↓-ap-in (λ x → Param P x _)
                        (λ x → μ-bsd (ψp k x))
                        lem ∙ᵈ
           μ-lf-invar (ϕ k p₀) (κp k p₀) _ l₁)

      --
      --  Full substitution invariance
      --

      μ-bsd-flatn-invar : {i : I} {f : Op P i} (pd : W (P // R) (i , f))
        → μ-bsd (flatn R pd) == f
        
      μ-bsd-flatn-invar-frm : {f : Ops P} (pd : W (P // R) f)
        → μ-bsd-frm (flatn R pd) == flatn-frm R pd [ Frame P (flatn R pd) ↓ μ-bsd-flatn-invar pd ]

      μ-bsd-flatn-invar (lf (i , f)) = unit-l f
      μ-bsd-flatn-invar (nd (((w , ._) , idp) , κ)) =
        let κ' g n = (flatn R (κ g n) , flatn-frm R (κ g n)) ,
                            pair= (μ-bsd-flatn-invar (κ g n))
                                  (μ-bsd-flatn-invar-frm (κ g n))
        in μ-subst-invar w κ'

      μ-bsd-flatn-invar-frm (lf (i , f)) = ↓-Op-Frame-in P (unit-l f) lem
        where lem : (j : I) (l : Leaf P (corolla P f) j)
                → –> (μ-bsd-frm (corolla P f) j) l ==
                  –> (corolla-frm P f j) l [ (λ x → Param P x j) ↓ unit-l f ]
              lem j (j , p , idp) = unit-l-frm f j p

      μ-bsd-flatn-invar-frm (nd (((w , ._) , idp) , κ)) =
        ↓-Op-Frame-in P (μ-subst-invar w κ')
                        (μ-lf-invar w κ')

        where κ' : (g : Ops P) (n : Node P w g) → Σ (InFrame P g) (R g)
              κ' g n = (flatn R (κ g n) , flatn-frm R (κ g n)) , 
                              pair= (μ-bsd-flatn-invar (κ g n))
                                    (μ-bsd-flatn-invar-frm (κ g n))

      -- Finally, the main result: the biased laws imply
      -- subdivision invariance.
      μ-bsd-invar : SubInvar R
      μ-bsd-invar pd = pair= (μ-bsd-flatn-invar pd)
                             (μ-bsd-flatn-invar-frm pd) 

  -- In the following we show that given a PolyMagma we can obtain a biased magma satisfying the biased laws 
  module _ {ℓ} {I : Type ℓ} {P : Poly I} (Mgm : PolyMagma P) (laws : SubInvar ⟪ Mgm ⟫ ) where

    open BiasedMgm
    open BiasedLaws
  
    biased-mgm : BiasedMgm P
    η     biased-mgm i     = μ Mgm (lf i)
    η-frm biased-mgm i     = μ-frm Mgm (lf i)
    γ     biased-mgm f ϕ   = μ Mgm (nd (f , λ j l → corolla P (ϕ j l)))
    γ-frm biased-mgm f ϕ j = (μ-frm Mgm w j) ∘e equiv (λ { (k , p , q) → (k , p , (j , q , idp)) }) (λ { (k , p , (_ , q , idp)) → (k , p , q)}) (λ { (_ , _ , (_ , _ , idp)) → idp}) (λ _ → idp)
      where 
        w = nd (f , λ k l → corolla P (ϕ k l))

    module left-laws {i : I} (f : Op P i) where

      w : W P i
      w = nd (f , λ j _ → corolla P (η biased-mgm j))

      pd : W (P // ⟪ Mgm ⟫) (i , μ Mgm w)
      pd = nd (((w , μ-frm Mgm _) , pair= idp idp) , κ)
        where κ : (g : Ops P) (n : Node P w g) → W (P // ⟪ Mgm ⟫) g
              κ g (inl idp) = lf g
              κ g (inr (_ , _ , inl idp)) = corolla (P // ⟪ Mgm ⟫) ((lf (fst g) , μ-frm Mgm _), pair= idp idp) 
              κ g (inr (_ , _ , inr ()))

      lem : (μ Mgm w , flatn-frm ⟪ Mgm ⟫ pd) == (f , flatn-frm ⟪ Mgm ⟫ (lf (_ , f)))
      lem = ! (laws pd) ∙ laws (lf (_ , f))

      unit-l-law : γ biased-mgm f (λ j _ → η biased-mgm j) == f
      unit-l-law = fst= lem

      unit-l-frm-law : (j : I) (p : Param P f j)
        → γ-frm-to biased-mgm (j , p , –> (η-frm biased-mgm j j) idp) == p [ (λ x → Param P x j) ↓ unit-l-law ]
      unit-l-frm-law j p = apd (λ { (_ , fr) → –> (fr j) (j , p , idp) }) lem
        >> ↓-ap-in (λ x → Param P x j) fst

    module right-laws {i : I} (ϕ : (j : I) → Param P (η biased-mgm i) j → Op P j) where

      w : W P i
      w = nd (η biased-mgm i , λ j p → corolla P (ϕ j p))

      f = ϕ i (–> (η-frm biased-mgm i i) idp)

      pd : W (P // ⟪ Mgm ⟫) (i , μ Mgm w)
      pd = nd (((w , μ-frm Mgm _) , pair= idp idp) , κ)
        where κ : (g : Ops P) (n : Node P w g) → W (P // ⟪ Mgm ⟫) g
              κ g (inl idp) = corolla (P // ⟪ Mgm ⟫) ((lf (fst g) , μ-frm Mgm _), pair= idp idp)
              κ g (inr (_ , _ , inl idp)) = lf g
              κ g (inr (_ , _ , inr ()))
      
      lem : (f , flatn-frm ⟪ Mgm ⟫ (lf (_ , f))) == (μ Mgm w , flatn-frm ⟪ Mgm ⟫ pd)
      lem = ! (laws (lf (_ , f))) ∙ (laws pd)

      unit-r-law : ϕ i (–> (η-frm biased-mgm i i) idp) == γ biased-mgm (η biased-mgm i) ϕ
      unit-r-law = fst= lem

      unit-r-frm-law : (j : I) (p : Param P (ϕ i (–> (η-frm biased-mgm i i) idp)) j)
        → p == γ-frm-to biased-mgm (i , –> (η-frm biased-mgm i i) idp , p) [ (λ x → Param P x j) ↓ unit-r-law ]
      unit-r-frm-law j p = apd (λ { (_ , fr) → –> (fr j) (j , p , idp) }) lem
        >> ↓-ap-in (λ x → Param P x j) fst

    module assoc-laws
      {i : I}
      (f : Op P i)
      (ϕ : (j : I) → Param P f j → Op P j)
      (ψ : (j : I) → Σ I (λ k → Σ (Param P f k) (λ p → Param P (ϕ k p) j)) → Op P j) where 
     
      -- left case
      lhs = γ biased-mgm (γ biased-mgm f ϕ) (λ k q → ψ k (_ , _ , γ-frm-snd-param biased-mgm q))

      left-w = nd (γ biased-mgm f ϕ , λ k q → corolla P (ψ k (_ , _ , γ-frm-snd-param biased-mgm q)))
          
      left-nd₁ = corolla (P // ⟪ Mgm ⟫) ((nd (f , λ j p → corolla P (ϕ j p)) , μ-frm Mgm _) , pair= idp idp)

      left-κ : (f : Ops P) (n : Node P left-w f) → W (P // ⟪ Mgm ⟫) f
      left-κ _ (inl idp)               = left-nd₁
      left-κ _ (inr (k , q , inl idp)) = lf (k , ψ k (_ , _ , γ-frm-snd-param biased-mgm q))
      left-κ _ (inr (_ , _ , inr (_ , _ , ()))) 

      left-pd : W (P // ⟪ Mgm ⟫) (i , lhs)
      left-pd = nd (((left-w , μ-frm Mgm _) , pair= idp idp) , left-κ)

      -- right case
      rhs = γ biased-mgm f (λ j p → γ biased-mgm (ϕ j p) (λ k q → ψ k (_ , _ , q)))

      right-w = nd (f , λ j p → corolla P (γ biased-mgm (ϕ j p) (λ k q → ψ k (_ , _ , q))))
                                                                                    
      right-nd : (j : I) → (p : Param P f j) → W (P // ⟪ Mgm ⟫) (j , _)
      right-nd j p  = corolla (P // ⟪ Mgm ⟫) ((nd (ϕ j p , λ k q → corolla P (ψ k (_ , _ , q))) , μ-frm Mgm _) , pair= idp idp)

      right-κ : (f : Ops P) (n : Node P right-w f) → W (P // ⟪ Mgm ⟫) f 
      right-κ _ (inl idp)               = lf (_ , f)
      right-κ _ (inr (j , p , inl idp)) = right-nd j p
      right-κ _ (inr (_ , _ , inr (_ , _ , ()))) 

      right-pd : W (P // ⟪ Mgm ⟫) (i , rhs)
      right-pd = nd (((right-w , μ-frm Mgm _) , pair= idp idp) , right-κ)          

      -- flatn lhs = flatn rhs

      lem-ψ :
        (λ (j : I)
           (p : Param P f j)
           (k : I)
           (q : Param P (ϕ j p) k)
           → ((j , p , q) , λ (l : I) (r : Param P (ψ k (j , p , q)) l) → r))
        ==
        (λ (j : I)
           (p : Param P f j)
           (k : I)
           (q : Param P (ϕ j p) k)
           → (γ-frm-from biased-mgm (γ-frm-to biased-mgm (j , p , q)) , λ (l : I) (r : Param P (ψ k (j , p , q)) l) → transport! (λ x → Param P (ψ k x) l) (<–-inv-l (γ-frm biased-mgm f ϕ k) (j , p , q)) r))
      lem-ψ = let pth j p k q = ↓-Π-cst-app-in  λ l → ↓-Π-cst-app-in λ r → !ᵈ (to-transp!!-↓ (λ x → Param P (ψ k x) l) (<–-inv-l (γ-frm biased-mgm f ϕ k) (j , p , q)) r)
        in λ= λ j → λ= λ p → λ= λ k → λ= λ q → pair= (! (<–-inv-l (γ-frm biased-mgm f ϕ k) (j , p , q))) (pth j p k q)

      -- Simple proof of assoc-flatn which doesn't rely on lem-ψ but not convenient to work with when we want to prove assoc-frm-law
      -- assoc-flatn : flatn ⟪ Mgm ⟫ right-pd == flatn ⟪ Mgm ⟫ left-pd
      -- assoc-flatn = ap (λ x → nd (f , x)) (λ= λ j → λ= λ p → ap (λ y → nd (ϕ j p , y)) (λ= λ m → λ= λ q → ap (λ { (j' , p' , q') → corolla P (ψ m (j' , p' , q')) }) (! (<–-inv-l (γ-frm biased-mgm f ϕ m) (j , p , q)))))

      assoc-flatn : flatn ⟪ Mgm ⟫ right-pd == flatn ⟪ Mgm ⟫ left-pd
      assoc-flatn = ap (λ g → nd (f , λ j p → nd (ϕ j p , λ k q → corolla P (ψ k (fst (g j p k q)))))) lem-ψ

      lem : (rhs , flatn-frm ⟪ Mgm ⟫ right-pd) == (lhs , flatn-frm ⟪ Mgm ⟫ left-pd) [ OutFrame P ↓ assoc-flatn ]
      lem = ! (laws right-pd) ∙ᵈ apd (λ x → (μ Mgm x , μ-frm Mgm x)) assoc-flatn ∙ᵈ (laws left-pd)
        >> transport (λ x → (rhs , flatn-frm ⟪ Mgm ⟫ right-pd) == (lhs , flatn-frm ⟪ Mgm ⟫ left-pd) [ OutFrame P ↓ x ]) (∙-unit-r assoc-flatn)

      -- Our magma is associative
      assoc-law : γ biased-mgm f (λ j p → γ biased-mgm (ϕ j p) (λ k q → ψ k (j , p , q))) == γ biased-mgm (γ biased-mgm f ϕ) (λ j p → ψ j (<– (γ-frm biased-mgm f ϕ j) p))
      assoc-law = ↓-cst-out (ap↓ fst lem) 

      -- The frames are coherent w.r.t. assoc
      assoc-frm-law :
        (l : I)
        (j : I) (p : Param P f j)
        (k : I) (q : Param P (ϕ j p) k)
        (r : Param P (ψ k (j , p , q)) l)
        → γ-frm-to biased-mgm (j , p , γ-frm-to biased-mgm (k , q , r)) ==
          γ-frm-to biased-mgm (k , γ-frm-to biased-mgm (j , p , q) , transport! (λ x → Param P (ψ k x) l) (<–-inv-l (γ-frm biased-mgm f ϕ k) (j , p , q)) r)
          [ (λ x → Param P x l) ↓ assoc-law ]
      assoc-frm-law l j p k q r = ↓-Π-out lf-to-par-pth lf-pth
        >> ↓-cst2-out _ _ 
        >> ↓-ap-in _ _
        >> transport (λ x → γ-frm-to biased-mgm (j , p , γ-frm-to biased-mgm (k , q , r)) == γ-frm-to biased-mgm (k , γ-frm-to biased-mgm (j , p , q) , transport! (λ x → Param P (ψ k x) l) (<–-inv-l (γ-frm biased-mgm f ϕ k) (j , p , q)) r) [ (λ x → Param P x l) ↓ x ]) (lem-ap-pair assoc-flatn lem)
        where kpq-r : Leaf P (flatn ⟪ Mgm ⟫ right-pd) l
              kpq-r = (j , p , (k , q , (l , r , idp)))

              kpq-l : Leaf P (flatn ⟪ Mgm ⟫ left-pd) l
              kpq-l = (j , p , (k , q , (l , transport! (λ x → Param P (ψ k x) l) (<–-inv-l (γ-frm biased-mgm f ϕ k) (j , p , q)) r , idp)))

              lf-to-par-pth : –> (flatn-frm ⟪ Mgm ⟫ right-pd l) == –> (flatn-frm ⟪ Mgm ⟫ left-pd l) [ (λ { (x , (y , z)) → Leaf P x l → Param P y l })  ↓ pair= assoc-flatn lem ]
              lf-to-par-pth = apd↓ (λ { (_ , fr) → –> (fr l)  }) lem

              lf-pth : kpq-r == kpq-l [ (λ { (x , _) → Leaf P x l}) ↓ pair= assoc-flatn lem ]
              lf-pth = apd (λ g → (j , p , (k , q , (l , snd (g j p k q) l r , idp)))) lem-ψ
                >> ↓-ap-in (λ x → Leaf P x l) (λ g → nd (f , λ j p → nd (ϕ j p , λ k q → corolla P (ψ k (fst (g j p k q))))))
                >> ↓-cst2-in assoc-flatn lem
                                         
              lem-ap-pair : ∀ {i j} {A B : Type i} {C : A → B → Type j}
                {x x' : A} (p : x == x')
                {y y' : B} {z : C x y} {z' : C x' y'}
                (q : (y , z) == (y' , z') [ (λ x → Σ B (C x)) ↓ p ])
                → ap (fst ∘ snd) (pair= p q) == ↓-cst-out (ap↓ fst q)
              lem-ap-pair idp idp = idp 
            

    -- Finally, we pack the laws altogether

    biased-mgm-laws : BiasedLaws P biased-mgm
    unit-l     biased-mgm-laws = unit-l-law
     where open left-laws
    unit-r     biased-mgm-laws = unit-r-law
      where open right-laws
    assoc      biased-mgm-laws = assoc-law
      where open assoc-laws
    unit-l-frm biased-mgm-laws = unit-l-frm-law
      where open left-laws
    unit-r-frm biased-mgm-laws = unit-r-frm-law
      where open right-laws
    assoc-frm  biased-mgm-laws = assoc-frm-law
      where open assoc-laws
