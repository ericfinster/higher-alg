{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Grafting
open import Biased

module wip.SubstitutionLaws {ℓ} {I : Type ℓ} (P : Poly I) (R : PolyRel P) where

  open import Substitution P
  open BiasedMgm
  open BiasedLaws

  subst-η : {i : I} (f : Op P i) → InFrame P (i , f)
  subst-η f = corolla P f , corolla-frm P f

  subst-γ : {i : I} (f : Op P i)
    → (w : W P i) (α : Frame P w f) 
    → (κ : (g : Ops P) → Node P w g → Σ (InFrame P g) (R g))
    → InFrame P (i , f)
  subst-γ f w α κ = 
    let κ' g n = fst (κ g n)
    in (subst w κ' , λ j → α j ∘e subst-lf-eqv w κ' j) 

  subst-η-frm : (f g : Ops P)
    → (f == g) ≃ (f == g) ⊔ Σ I (λ k → Σ (Param P (snd f) k) (λ p → Lift {j = ℓ} ⊥))
  subst-η-frm f g = equiv inl from to-from (λ _ → idp)

    where from : (f == g) ⊔ Σ I (λ k → Σ (Param P (snd f) k) (λ p → Lift ⊥)) → f == g
          from (inl e) = e
          from (inr (_ , _ , ()))

          to-from : (e : (f == g) ⊔ Σ I (λ k → Σ (Param P (snd f) k) (λ p → Lift ⊥)))
            → inl (from e) == e
          to-from (inl e) = idp
          to-from (inr (_ , _ , ()))


  -- The extra information required from a relation in order that we
  -- can construct a biased multiplication on the slice by R.
  record SubstRel : Type ℓ where
    field

      η-rel : {i : I} (f : Op P i) → R (i , f) (subst-η f)
      γ-rel : {i : I} (f : Op P i) (w : W P i) (α : Frame P w f) (r : R (i , f) (w , α))
                → (κ : (j : Ops P) → Node P w j → Σ (InFrame P j) (R j))
                → R (i , f) (subst-γ f w α κ)

  open SubstRel
  
  SubstBiasedMgm : SubstRel → BiasedMgm (P // R)
  η (SubstBiasedMgm SRel) (i , f) =
    subst-η f , η-rel SRel f
  η-frm (SubstBiasedMgm SRel) =
    subst-η-frm
  γ (SubstBiasedMgm SRel) {i , f} ((w , α) , r) κ =
    subst-γ f w α κ , γ-rel SRel f w α r κ
  γ-frm (SubstBiasedMgm SRel) ((w , α) , r) κ g =
    -- This might indicate that you have not chosen the
    -- most natural direction for the subst-nd equivalence...
    (subst-nd-eqv  w (λ g n → fst (κ g n)) g)⁻¹

  --
  --  Substitution Laws
  --

  subst-unit-l : {i : I} (w : W P i)
    → subst w (λ g n → corolla P (snd g) , corolla-frm P (snd g)) == w
  subst-unit-l (lf i) = idp
  subst-unit-l (nd (f , ϕ)) = ap (λ x → nd (f , x))
    (Decor-== P (λ j p → subst-unit-l (ϕ j p)))

  subst-unit-l-frm : {i : I} {f : Op P i}
    → (w : W P i) (α : Frame P w f)
    → (λ j → α j ∘e subst-lf-eqv w (λ g n → subst-η (snd g)) j)
        == α [ (λ x → Frame P x f) ↓ subst-unit-l w ]
  subst-unit-l-frm (lf i) α = λ= (λ j → equiv-== (λ _ → idp))
  subst-unit-l-frm (nd (f₀ , ϕ)) α =
    ↓-W-Frame-in P (λ j l₀ l₁ r → ap (–> (α j)) {!SubstRelMgm!})

  subst-unit-r-frm : {i : I} {f : Op P i}
    → (κ : (g : Ops P) → Node P (corolla P f) g → Σ (InFrame P g) (R g))
    → (snd (fst (κ (i , f) (inl idp))))
        == (λ j → corolla-frm P f j ∘e subst-lf-eqv (corolla P f) (λ g n → fst (κ g n)) j)
             [ (λ x → Frame P x f) ↓ graft-unit P (fst (fst (κ (i , f) (inl idp)))) ]
  subst-unit-r-frm {i} {f} κ =
    let ((w , α) , r) = κ (i , f) (inl idp)
    in  graft-unit-frm P w α ∙'ᵈ {!!} 

  -- subst-graft : {i : I} (w : W P i) (ψ : ∀ j → Leaf P w j → W P j)
  --   → (κ : (g : Ops P) → Node P w g → Op Subst g)
  --   → (θ : (j : I) (l : Leaf P w j) (g : Ops P) → Node P (ψ j l) g → Op Subst g)
  --   → subst (graft P w ψ) (λ g → graft-node-rec P w ψ g (κ g) (λ j l n → θ j l g n)) ==
  --     graft P (subst w κ) (λ j → subst-lf-rec w κ j (λ l → subst (ψ j l) (θ j l)))
  -- subst-graft (lf i) ψ κ θ = subst-lf-rec-β (lf i) κ i (λ l → subst (ψ i l) (θ i l)) idp
  -- subst-graft {i} (nd (f , ϕ)) ψ κ θ = 
  --   let (w , α) = κ (_ , f) (inl idp)
  --       p j l₀ = –> (α j) l₀
  --       ψ' j l₀ k l₁ = ψ k (j , p j l₀ , l₁)
  --       κ' j l₀ g n = κ g (inr (j , p j l₀ , n))
  --       θ' j l₀ k l₁ g n = θ k (j , p j l₀ , l₁) g n
  --       ψ₀ j l₀ = subst (ϕ j (p j l₀)) (κ' j l₀)
  --       ψ₁ k j l₀ l₁ = subst-lf-rec (ϕ j (p j l₀)) (κ' j l₀) k (λ l₁ → subst (ψ' j l₀ k l₁) (θ' j l₀ k l₁)) l₁
  --   in graft P w (λ j l₀ → subst (graft P (ϕ j (p j l₀)) (ψ' j l₀))
  --                (λ g → graft-node-rec P (ϕ j (p j l₀)) (ψ' j l₀) g (κ' j l₀ g) (λ k l₁ n → θ' j l₀ k l₁ g n))) 
  --        -- By the induction hypothesis ...                 
  --        =⟨ ap (graft P w) (λ= (λ j → (λ= (λ l₀ → subst-graft (ϕ j (p j l₀)) (ψ' j l₀) (κ' j l₀) (θ' j l₀))))) ⟩ 
  --      graft P w (λ j l₀ → graft P (subst (ϕ j (p j l₀)) (κ' j l₀)) (λ k → ψ₁ k j l₀)) 
  --        -- By graft associativity ...       
  --        =⟨ ! (graft-assoc P w ψ₀ ψ₁) ⟩ 
  --      graft P (graft P w ψ₀) (λ k → graft-leaf-rec P w ψ₀ k (ψ₁ k))
  --        -- Because recursion commutes with composition ... (is there an easier way?)
  --        =⟨ ap (graft P (graft P w ψ₀)) (λ= (λ j → λ= (λ l → graft-leaf-rec-∘ P (λ l₀ → subst (ψ j l₀) (θ j l₀)) w ψ₀ j
  --           (λ k l₀ l₁ → k , –> (α k) l₀ , subst-lf-to (ϕ k (–> (α k) l₀)) (κ' k l₀) j l₁) l ))) ⟩
  --      graft P (graft P w ψ₀) (λ j → subst-lf-rec (nd (f , ϕ)) κ j (λ l → subst (ψ j l) (θ j l))) ∎

  subst-assoc : {i : I} (w : W P i) 
    → (κ : (g : Ops P) → Node P w g → Σ (InFrame P g) (R g))
    → (ν : (j : Ops P) → Σ (Ops P) (λ k → Σ (Node P w k) (λ p → Node P (fst (fst (κ k p))) j)) →
                         Σ (InFrame P j) (R j))
    → subst w (λ g n → subst-γ (snd g) (fst (fst (κ g n))) (snd (fst (κ g n))) (λ g' n' → ν g' (g , n , n')))
      == subst (subst w (λ g n → fst (κ g n))) (λ g' n' → fst (ν g' (subst-nd-to w (λ g n → fst (κ g n)) g' n')))
  subst-assoc (lf i) κ ν = idp
  subst-assoc (nd (f , ϕ)) κ ν = 
    let ((w , α) , r) = κ (_ , f) (inl idp)
        p j l = –> (α j) l
        κ' j l g n = fst (κ g (inr (j , p j l , n)))
        ψ j l = subst (ϕ j (p j l)) (κ' j l)
        κ₁ g n = subst-γ (snd g) (fst (fst (κ g n))) (snd (fst (κ g n))) (λ g' n' → ν g' (g , n , n'))
        κ₁' j l g n = κ₁ g (inr (j , –> (snd (κ₁ (_ , f) (inl idp)) j) l , n))
    in graft P (fst (κ₁ (_ , f) (inl idp))) (λ j l → subst (ϕ j (–> (snd (κ₁ (_ , f) (inl idp)) j) l)) (κ₁' j l ))
         =⟨ idp ⟩
       graft P (subst w (λ g' n' → fst (ν g' ((_ , f) , inl idp , n')))) (λ j l → subst (ϕ j (–> (snd (κ₁ (_ , f) (inl idp)) j) l)) (κ₁' j l ))
         =⟨ idp ⟩ 
       graft P (subst w (λ g' n' → fst (ν g' ((_ , f) , inl idp , n')))) (λ j l → subst (ϕ j (–> (snd (κ₁ (_ , f) (inl idp)) j) l)) (κ₁' j l ))        
         =⟨ {!!} ⟩
       subst (graft P w ψ) (λ g' n' → fst (ν g' (subst-nd-to (nd (f , ϕ)) (λ g n → fst (κ g n)) g' n'))) ∎


  -- subst-nd-to (nd (f , ϕ)) κ g n | inl n' = (_ , f) , inl idp , n'
  -- subst-nd-to (nd (f , ϕ)) κ g n | inr (k , l , n') = 
  --   let (w , α) = κ (_ , f) (inl idp)
  --       κ' j l g n = κ g (inr (j , –> (α j) l , n))
  --       ψ j l = subst (ϕ j (–> (α j) l)) (κ' j l)
  --       (h , n₀ , n₁) = subst-nd-to (ϕ k (–> (α k) l)) (κ' k l) g n'
  --   in h , (inr (k , –> (α k) l , n₀)) , n₁

  -- subst-γ : {i : I} (f : Op P i)
  --   → (w : W P i) (α : Frame P w f) 
  --   → (κ : (g : Ops P) → Node P w g → Σ (InFrame P g) (R g))
  --   → InFrame P (i , f)
  -- subst-γ f w α κ = 
  --   let κ' g n = fst (κ g n)
  --   in (subst w κ' , λ j → α j ∘e subst-lf-eqv w κ' j) 

  -- subst (nd (f , ϕ)) κ =
  --   let (w , α) = κ (_ , f) (inl idp)
  --       κ' j l g n = κ g (inr (j , –> (α j) l , n))
  --       ψ j l = subst (ϕ j (–> (α j) l)) (κ' j l)
  --   in graft P w ψ

  -- And old version ....
  -- subst-assoc : {i : I} (w : W P i)
  --   → (κ₀ : (g : Ops P) → Node P w g → Op Subst g)
  --   → (κ₁ : (h : Ops P) (n : Node P w h) (g : Ops P) → Node P (fst (κ₀ h n)) g → Op Subst g)
  --   → subst (subst w κ₀) (λ g → subst-nd-rec w κ₀ g (λ { (h , n₀ , n₁) → κ₁ h n₀ g n₁ }))  ==
  --     subst w (λ h n₀ → subst (fst (κ₀ h n₀)) (κ₁ h n₀) , λ j → (snd (κ₀ h n₀)) j ∘e subst-lf-eqv (fst (κ₀ h n₀)) (κ₁ h n₀) j)
  -- subst-assoc (lf i) κ₀ κ₁ = idp
  -- subst-assoc (nd (f , ϕ)) κ₀ κ₁ = 
  --   let op = κ₀ (_ , f) (inl idp)
  --       p j l = –> (snd op j) l
  --       κ₀' j l g n = κ₀ g (inr (j , p j l , n))
  --       ψ₀ j l = subst (ϕ j (p j l)) (κ₀' j l)
  --   in subst (graft P (fst op) ψ₀) (λ g → subst-nd-rec (nd (f , ϕ)) κ₀ g (λ { (h , n₀ , n₁) → κ₁ h n₀ g n₁ }))
  --        =⟨ {!!} ⟩ 
  --      subst (nd (f , ϕ)) (λ h n₀ → subst (fst (κ₀ h n₀)) (κ₁ h n₀) , (λ j → snd (κ₀ h n₀) j ∘e subst-lf-eqv (fst (κ₀ h n₀)) (κ₁ h n₀) j)) ∎


  -- subst-assoc-frm : {i : I} {f : Op P i}
  --   → (w : W P i) (α : Frame P w f)
  --   → (κ : (g : Ops P) → Node P w g → Σ (InFrame P g) (R g))
  --   → (ν : (j : Ops P) → Σ (Ops P) (λ k → Σ (Node P w k) (λ p → Node P (fst (fst (κ k p))) j)) →
  --                        Σ (InFrame P j) (R j))
  --   → (λ j → α j ∘e subst-lf-eqv w (λ g n → subst-γ (snd g) (fst (fst (κ g n))) (snd (fst (κ g n))) (λ g' n' → ν g' (g , n , n'))) j) ==
  --     (λ j → α j ∘e subst-lf-eqv w (λ g n → fst (κ g n)) j ∘e subst-lf-eqv (subst w (λ g n → fst (κ g n))) (λ g' n' → fst (ν g' (subst-nd-to w (λ g n → fst (κ g n)) g' n'))) j)
  --       [ (λ x → Frame P x f) ↓ subst-assoc w κ ν ]                          
  -- subst-assoc-frm = {!!}

  record SubstRelLaws (SRel : SubstRel) : Type ℓ where
    field

      subst-unit-l-rel : {i : I} {f : Op P i}
        → (w : W P i) (α : Frame P w f) (r : R (i , f) (w , α))
        → γ-rel SRel f w α r (λ g _ → η (SubstBiasedMgm SRel) g)
            == r [ R (i , f) ↓ pair= (subst-unit-l w) (subst-unit-l-frm w α) ]

      subst-unit-r-rel : {i : I} {f : Op P i}
        → (κ : (g : Ops P) → Node P (corolla P f) g → Σ (InFrame P g) (R g))
        → snd (κ (i , f) (inl idp)) == γ-rel SRel f (corolla P f) (corolla-frm P f) (η-rel SRel f) κ
            [ R (i , f) ↓ pair= (graft-unit P (fst (fst (κ (i , f) (inl idp))))) (subst-unit-r-frm κ) ]

  open SubstRelLaws
  
  SubstBiasedLaws : (SRel : SubstRel) (SLaws : SubstRelLaws SRel)
    → BiasedLaws (P // R) (SubstBiasedMgm SRel)
  unit-l (SubstBiasedLaws SRel SLaws) ((w , α) , r) =
    pair= (pair= (subst-unit-l w) (subst-unit-l-frm w α))
          (subst-unit-l-rel SLaws w α r)
  unit-r (SubstBiasedLaws SRel SLaws) {i , f} κ =
    let ((w , α) , r) = κ (i , f) (inl idp)
    in pair= (pair= (graft-unit P w) (subst-unit-r-frm κ))
             (subst-unit-r-rel SLaws κ)
  assoc (SubstBiasedLaws SRel SLaws) ((w , α) , r) κ ν =
    pair= (pair= (subst-assoc w κ ν) {!!})
          {!!}
  unit-l-frm (SubstBiasedLaws SRel SLaws) ((w , α) , r) g n = {!!}
  unit-r-frm (SubstBiasedLaws SRel SLaws) κ g n = {!!}
  assoc-frm (SubstBiasedLaws SRel SLaws) = {!!}




