{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import PolyMagma
open import Grafting
open import Substitution

-- Slicing a polynomial by a relation, etc.
module Slice where

  -- The slice of a polynomial by a relation
  _//_ : ∀ {ℓ} {I : Type ℓ} (P : Poly I) (R : PolyRel P) → Poly (Ops P)
  Op (P // R) f = Σ (InFrame P f) (R f)
  Param (P // R) ((w , _) , _) = Node P w

  -- Forgetting from the slice
  module _ {ℓ} {I : Type ℓ} (P : Poly I) (R : PolyRel P) where

    W↓ : {f : Ops P} → W (P // R) f → W (Subst P) f
    W↓ (lf f) = lf f
    W↓ (nd ((wα , r) , ϕ)) = nd (wα , λ g n → W↓ (ϕ g n))

    W↓-lf-to : {f : Ops P} (pd : W (P // R) f) (g : Ops P)
      → Leaf (Subst P) (W↓ pd) g → Leaf (P // R) pd g 
    W↓-lf-to (lf i) g l = l
    W↓-lf-to (nd (wαr , ϕ)) g (h , n , l) =
      h , n , W↓-lf-to (ϕ h n) g l

    W↓-lf-from : {f : Ops P} (pd : W (P // R) f) (g : Ops P)
      → Leaf (P // R) pd g → Leaf (Subst P) (W↓ pd) g
    W↓-lf-from (lf i) g l = l
    W↓-lf-from (nd (wαr , ϕ)) g (h , n , l) =
      h , n , W↓-lf-from (ϕ h n) g l

    W↓-lf-to-from : {f : Ops P} (pd : W (P // R) f) (g : Ops P)
      → (l : Leaf (P // R) pd g)
      → W↓-lf-to pd g (W↓-lf-from pd g l) == l
    W↓-lf-to-from (lf i) g l = idp
    W↓-lf-to-from (nd (wαr , ϕ)) g (h , n , l) =
      ap (λ x → h , n , x) (W↓-lf-to-from (ϕ h n) g l)

    W↓-lf-from-to : {f : Ops P} (pd : W (P // R) f) (g : Ops P)
      → (l : Leaf (Subst P) (W↓ pd) g)
      → W↓-lf-from pd g (W↓-lf-to pd g l) == l
    W↓-lf-from-to (lf i) g l = idp
    W↓-lf-from-to (nd (wαr , ϕ)) g (h , n , l) =
      ap (λ x → h , n , x) (W↓-lf-from-to (ϕ h n) g l)
  
    W↓-lf-eqv : {f : Ops P} (pd : W (P // R) f) (g : Ops P)
      → Leaf (Subst P) (W↓ pd) g ≃ Leaf (P // R) pd g 
    W↓-lf-eqv pd g = equiv (W↓-lf-to pd g) (W↓-lf-from pd g)
      (W↓-lf-to-from pd g) (W↓-lf-from-to pd g)

    -- These two are part of an equivalence between frames ...
    Frame↓ : {f : Ops P} {wαr : Op (P // R) f} {pd : W (P // R) f}
      → Frame (P // R) pd wαr
      → Frame (Subst P) (W↓ pd) (fst wαr)
    Frame↓ {pd = pd} β g = (β g) ∘e W↓-lf-eqv pd g

    Frame↑ : {f : Ops P} {wαr : Op (P // R) f} {pd : W (P // R) f}
      → Frame (Subst P) (W↓ pd) (fst wαr)
      → Frame (P // R) pd wαr
    Frame↑ {pd = pd} β g = β g ∘e (W↓-lf-eqv pd g)⁻¹ 

    -- Exactly.  And this is the new version of being
    -- subdivision invariant.
    SubInvar : Type ℓ
    SubInvar = {f : Ops P} (pd : W (P // R) f)
      → R f (μ-subst P (W↓ pd))

    SlcMgm : SubInvar → PolyMagma (P // R)
    μ (SlcMgm Ψ) pd = μ-subst P (W↓ pd) , Ψ pd
    μ-frm (SlcMgm Ψ) pd = Frame↑ {wαr = μ-subst P (W↓ pd) , Ψ pd} {pd = pd} (μ-frm-subst P (W↓ pd))

    -- The extra information required from a relation in order that we
    -- can construct a biased multiplication on the slice by R.
    record BiasedRel : Type ℓ where
      field

        η-rel : (f : Ops P) → R f (subst-η P f)

        γ-rel : (f : Ops P) (wα : InFrame P f) (r : R f wα)
          → (κ : Decor (P // R) (wα , r) (Op (P // R)))
          → R f (subst-γ P f wα (λ g n → fst (κ g n)))

    open BiasedRel

    -- A biased relation becomes subdivision invariant
    -- by iteration.
    ToSubInvar : BiasedRel → SubInvar
    ToSubInvar Ψ (lf f) = η-rel Ψ f
    ToSubInvar Ψ (nd ((wα , r) , ϕ)) =
      γ-rel Ψ _ wα r (λ g n → μ-subst P (W↓ (ϕ g n)) , ToSubInvar Ψ (ϕ g n))

  -- Proving subdivision invariance for a biased magma
  module _ {ℓ} {I : Type ℓ} {P : Poly I} (B : BiasedMgm P) where
  
    record BiasedLaws : Type ℓ where

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

    module _ (L : BiasedLaws) where

      private
        R = ⟪ BsdMgm B ⟫ 

      open BiasedMgm B
      open BiasedLaws L

      μ-graft-inv : {i : I} (w : W P i)
        → (ψ : ∀ j → Leaf P w j → W P j)
        → μ-bsd B (graft P w ψ) ==
          γ (μ-bsd B w) (λ j p → μ-bsd B (ψ j (<– (μ-bsd-frm B w j) p)))
      μ-graft-inv (lf i) ψ =
        let ψ' j p = μ-bsd B (ψ j (<– (μ-bsd-frm B (lf i) j) p))
        in ap (λ q → μ-bsd B (ψ i q)) (! (<–-inv-l (η-frm i i) idp)) ∙ unit-r ψ'  
      μ-graft-inv (nd (f , ϕ)) ψ = 
        let ih j p = μ-graft-inv (ϕ j p) (λ k l → ψ k (j , p , l))
            ϕ' j p = μ-bsd B (ϕ j p)
            ψ' j kpq = let (k , p , q) = kpq in μ-bsd B (ψ j (k , p , <– (μ-bsd-frm B (ϕ k p) j) q))
        in ap (γ f) (Decor-== P ih) ∙ assoc f ϕ' ψ'
        -- in γ f (λ j p → μ-bsd B (graft P (ϕ j p) (λ k l → ψ k (j , p , l))))
        --      =⟨ ap (γ f) (Decor-== P ih) ⟩
        --    γ f (λ j p → γ (μ-bsd B (ϕ j p)) (λ k q → μ-bsd B (ψ k (j , p , <– (μ-bsd-frm B (ϕ j p) k) q))))
        --      =⟨ assoc f ϕ' ψ' ⟩
        --    γ (γ f (λ j p → μ-bsd B (ϕ j p))) (λ j p → μ-bsd B (ψ j (<– (μ-bsd-frm B (nd (f , ϕ)) j) p))) ∎

      μ-graft-lf-param : {i : I} (w : W P i)
        → (ψ : ∀ j → Leaf P w j → W P j)
        → (j : I) (l : Leaf P (graft P w ψ) j)
        → Param P (γ (μ-bsd B w) (λ j p → μ-bsd B (ψ j (<– (μ-bsd-frm B w j) p)))) j
      μ-graft-lf-param w ψ j l = 
        let (k , l₀ , l₁) = <– (graft-leaf-eqv P w ψ j) l
        in γ-frm-to B (k , –> (μ-bsd-frm B w k) l₀ ,
          transport! (λ x → Param P (μ-bsd B (ψ k x)) j)
                     (<–-inv-l (μ-bsd-frm B w k) l₀)
                     (–> (μ-bsd-frm B (ψ k l₀) j) l₁))

      μ-graft-lf-inv : {i : I} (w : W P i)
        → (ψ : ∀ j → Leaf P w j → W P j)
        → (j : I) (l : Leaf P (graft P w ψ) j)
        → –> (μ-bsd-frm B (graft P w ψ) j) l == μ-graft-lf-param w ψ j l
            [ (λ x → Param P x j) ↓ μ-graft-inv w ψ ]
      μ-graft-lf-inv (lf i) ψ j l =
        let ψ' j p = μ-bsd B (ψ j (<– (μ-bsd-frm B (lf i) j) p))
        in ↓-ap-in (λ x → Param P x j) (λ q → μ-bsd B (ψ i q))
                   (to-transp!-↓ (λ x → Param P (μ-bsd B (ψ i x)) j)
                                 (<–-inv-l (μ-bsd-frm B (lf i) i) idp)
                                 (–> (μ-bsd-frm B (ψ i idp) j) l)) ∙ᵈ
           unit-r-frm ψ' j (transport! (λ pth → Param P (μ-bsd B (ψ i pth)) j)
                                       (<–-inv-l (μ-bsd-frm B (lf i) i) idp)
                                       (–> (μ-bsd-frm B (ψ i idp) j) l)) 
  
      -- I think this could be significantly cleaned up ...
      μ-graft-lf-inv (nd (f , ϕ)) ψ j (k , p , l) =
        let ih = μ-graft-lf-inv (ϕ k p) (λ k' l → ψ k' (k , p , l)) j l
            ϕ' j p = μ-bsd B (ϕ j p)
            ψ' j kpq = let (k , p , q) = kpq in μ-bsd B (ψ j (k , p , <– (μ-bsd-frm B (ϕ k p) j) q))
            (k₀ , l₀ , l₁) = <– (graft-leaf-eqv P (ϕ k p) (λ k' l' → ψ k' (k , p , l')) j) l
            p₀ = –> (μ-bsd-frm B (ϕ k p) k₀) l₀
            p₁ = –> (μ-bsd-frm B (ψ k₀ (k , p , l₀)) j) l₁

            pth₀ = μ-bsd-frm-from-to B (ϕ k p) k₀ l₀
            pth₁ = <–-inv-l (γ-frm f ϕ' k₀) (k , p , p₀)

            Q x = Param P (μ-bsd B (ψ k₀ x)) j

            t : Σ I (λ k₁ → Σ (Param P f k₁) (λ p₂ → Param P (μ-bsd B (ϕ k₁ p₂)) k₀)) →
                Σ I (λ k₁ → Σ (Param P f k₁) (λ p₂ → Leaf P (ϕ k₁ p₂) k₀))
            t x = let (k' , p' , q') = x in (k' , p' , <– (μ-bsd-frm B (ϕ k' p') k₀) q')

            s : Leaf P (ϕ k p) k₀  → Σ I (λ k₁ → Σ (Param P f k₁) (λ p₂ → Leaf P (ϕ k₁ p₂) k₀))
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
        → μ-bsd B (subst P w (λ g n → fst (κ g n))) == μ-bsd B w

      μ-subst-inv-lem : {i : I} (f : Op P i) (ϕ : Decor P f (W P))
        → (w : Op (P // R) (i , f))
        → (κ : (g : Ops P) → Node P (nd (f , ϕ)) g → Op (P // R) g)
        → μ-bsd B (graft P (fst (fst w))
                  (λ j l → subst P (ϕ j (–> (snd (fst w) j) l))
                  (λ g n → fst (κ g (inr (j , –> (snd (fst w) j) l , n)))))) ==
          γ f (λ j p → μ-bsd B (ϕ j p))

      μ-subst-invar (lf i) κ = idp
      μ-subst-invar (nd (f , ϕ)) κ =
        μ-subst-inv-lem f ϕ (κ (_ , f) (inl idp)) κ

      μ-subst-inv-lem ._ ϕ ((w , ._) , idp) κ = 
        let κp j p g n = κ g (inr (j , p , n))
            ψp j p = subst P (ϕ j p) (λ g n → fst (κp j p g n))
            ψ j l = ψp j (–> (μ-bsd-frm B w j) l)
            ih j p = ap (λ x → μ-bsd B (ψp j x)) (<–-inv-r (μ-bsd-frm B w j) p) ∙ μ-subst-invar (ϕ j p) (κp j p)
         in μ-graft-inv w ψ ∙ ap (γ (μ-bsd B w)) (Decor-== P ih)
        -- in μ-bsd B (graft P w ψ) 
        --      =⟨ μ-graft-inv w ψ ⟩
        --    γ (μ-bsd B w) (λ j p → μ-bsd B (ψp j (–> (μ-bsd-frm B w j) (<– (μ-bsd-frm B w j) p))))
        --      =⟨ λ= (λ j → λ= (λ p → ih j p)) |in-ctx (λ x → γ (μ-bsd B w) x) ⟩ 
        --    γ (μ-bsd B w) (λ j p → μ-bsd B (ϕ j p)) ∎


      -- Yeah, this needs some serious cleanup ...
      μ-lf-invar : {i : I} (w : W P i)
        → (κ : (g : Ops P) → Node P w g → Op (P // R) g)
        → (j : I) (l : Leaf P (subst P w (λ g n → fst (κ g n))) j)
        → –> (μ-bsd-frm B (subst P w (λ g n → fst (κ g n))) j) l  == 
          –> (μ-bsd-frm B w j ∘e (subst-leaf-eqv P w (λ g n → fst (κ g n)) j) ⁻¹) l
            [ (λ x → Param P x j) ↓ μ-subst-invar w κ ]

      μ-subst-leaf-inv-lem : {i j : I} (f : Op P i) (ϕ : Decor P f (W P))
        → (w : W P i) (α : Frame P w f) (r : R (i , f) (w , α))
        → (κ : (g : Ops P) → Node P (nd (f , ϕ)) g → Op (P // R) g)
        → (l : Leaf P (graft P w (λ j' l' → subst P (ϕ j' (–> (α j') l')) (λ g n → fst (κ g (inr (j' , (–> (α j') l') , n))) ))) j)
        → –> (μ-bsd-frm B (graft P w (λ j' l' → subst P (ϕ j' (–> (α j') l')) (λ g n → fst (κ g (inr (j' , (–> (α j') l') , n))) ))) j) l ==
          (let (k , l₀ , l₁) = graft-leaf-from P w (λ j' l' → subst P (ϕ j' (–> (α j') l')) (λ g n → fst (κ g (inr (j' , –> (α j') l' , n))))) j l
            in –> (γ-frm f (λ k p → μ-bsd B (ϕ k p)) j) (k , (–> (α k) l₀) ,
                 –> (μ-bsd-frm B (ϕ k (–> (α k) l₀)) j) (subst-leaf-from P (ϕ k (–> (α k) l₀)) (λ g n → fst (κ g (inr (k , (–> (α k) l₀) , n)))) j l₁)))
            [ (λ x → Param P x j) ↓ μ-subst-inv-lem f ϕ ((w , α) , r) κ ]

      μ-lf-invar (lf i) κ j l = idp
      μ-lf-invar (nd (f , ϕ)) κ j l =
        let ((w , α) , r) = κ (_ , f) (inl idp)
        in μ-subst-leaf-inv-lem f ϕ w α r κ l 


      μ-subst-leaf-inv-lem ._ ϕ w ._ idp κ l = 
        let κp j p g n = κ g (inr (j , p , n))
            ψp j p = subst P (ϕ j p) (λ g n → fst (κp j p g n))
            ψ j l = ψp j (–> (μ-bsd-frm B w j) l)
            (k , l₀ , l₁) = graft-leaf-from P w ψ _ l
            p₀ = –> (μ-bsd-frm B w k) l₀
            p₁ = –> (μ-bsd-frm B (ψp k p₀) _) l₁
            Q x = Param P (μ-bsd B (ψp k x)) _
            Q' x = Param P (μ-bsd B (ψp k (–> (μ-bsd-frm B w k) x))) _

            lem₀ = transport! Q' (<–-inv-l (μ-bsd-frm B w k) l₀) p₁
                     =⟨ transp!-ap Q (–> (μ-bsd-frm B w k)) (<–-inv-l (μ-bsd-frm B w k) l₀) p₁ ⟩
                   transport! Q (ap (–> (μ-bsd-frm B w k)) (<–-inv-l (μ-bsd-frm B w k) l₀)) p₁
                     =⟨ <–-inv-adj (μ-bsd-frm B w k) l₀ |in-ctx (λ x → transport! Q x p₁) ⟩ 
                   transport! Q (<–-inv-r (μ-bsd-frm B w k) p₀) p₁ ∎

            lem : transport! Q' (<–-inv-l (μ-bsd-frm B w k) l₀) p₁ == p₁ [ Q ↓ <–-inv-r (μ-bsd-frm B w k) p₀ ]
            lem = lem₀ ∙ᵈ to-transp!!-↓ Q (<–-inv-r (μ-bsd-frm B w k) p₀) p₁ 
            
        in μ-graft-lf-inv w ψ _ l ∙ᵈ
           ↓-γ-param' B (↓-ap-in (λ x → Param P x _)
                        (λ x → μ-bsd B (ψp k x))
                        lem ∙ᵈ
           μ-lf-invar (ϕ k p₀) (κp k p₀) _ l₁)

      --
      --  The associated biased relation
      --

      open BiasedRel
      
      LawsRel : BiasedRel P ⟪ BsdMgm B ⟫ 
      η-rel LawsRel (i , f) = pair= (unit-l f) (↓-Op-Frame-in P (unit-l f) lem)
        where lem : (j : I) (l : Leaf P (corolla P f) j)
                → –> (μ-bsd-frm B (corolla P f) j) l ==
                  –> (corolla-frm P f j) l [ (λ x → Param P x j) ↓ unit-l f ]
              lem j (k , p , idp) = unit-l-frm f k p
              
      γ-rel LawsRel (i , ._) (w , ._) idp κ =
        pair= (μ-subst-invar w κ) (↓-Op-Frame-in P (μ-subst-invar w κ)
                                                   (μ-lf-invar w κ))


      -- Subdivision invariance of the biased relation
      LawsInvar : SubInvar P ⟪ BsdMgm B ⟫
      LawsInvar = ToSubInvar P ⟪ BsdMgm B ⟫ LawsRel
