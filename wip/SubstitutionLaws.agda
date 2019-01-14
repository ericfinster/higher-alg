{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Biased

module wip.SubstitutionLaws {ℓ} {I : Type ℓ} (P : Poly I) (R : PolyRel P) where

  open import Substitution P
  open BiasedMgm
  open BiasedLaws

  -- The extra information required from a relation in order that we
  -- can construct a biased multiplication on the slice by R.

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


  record SubstRel : Type ℓ where
    field

      η-rel : {i : I} (f : Op P i) → R (i , f) (corolla P f , corolla-frm P f)
      γ-rel : {i : I} (f : Op P i) (w : W P i) (α : Frame P w f) (r : R (i , f) (w , α))
                → (κ : (j : Ops P) → Node P w j → Σ (InFrame P j) (R j))
                → R (i , f) (subst w (λ g n → fst (κ g n)) , λ j → α j ∘e subst-lf-eqv w (λ g n → fst (κ g n)) j)

  open SubstRel
  
  SubstBiasedMgm : SubstRel → BiasedMgm (P // R)
  η (SubstBiasedMgm SRel) (i , f) =
    subst-η f , η-rel SRel f
  η-frm (SubstBiasedMgm SRel) =
    subst-η-frm
  γ (SubstBiasedMgm SRel) {i , f} ((w , α) , r) κ =
    subst-γ f w α κ , γ-rel SRel f w α r κ
  γ-frm (SubstBiasedMgm SRel) ((w , α) , r) κ g =
    (subst-nd-eqv  w (λ g n → fst (κ g n)) g)⁻¹


  record SubstRelLaws : Type ℓ where

  subst-unit-l : {i : I} (w : W P i)
    → subst w (λ g n → corolla P (snd g) , corolla-frm P (snd g)) == w
  subst-unit-l (lf i) = idp
  subst-unit-l (nd (f , ϕ)) = ap (λ x → nd (f , x))
    (λ= (λ j → λ= (λ p → subst-unit-l (ϕ j p))))

  subst-unit-l-frm : {i : I} (f : Op P i)
    → (w : W P i) (α : Frame P w f)
    → (λ j → α j ∘e subst-lf-eqv w (λ g n → subst-η (snd g)) j)
        == α [ (λ x → Frame P x f) ↓ subst-unit-l w ]
  subst-unit-l-frm f (lf i) α = λ= (λ j → equiv-== (λ p → idp))
  subst-unit-l-frm f (nd x) α = {!!}

  -- ↓-W-Frame-in P (subst-unit-l w)
  --   (λ j → α j ∘e subst-lf-eqv w (λ g n → subst-η (snd g)) j) α
  --   (λ j l₀ l₁ → {!!})

  SubstBiasedLaws : (SRel : SubstRel) (SLaws : SubstRelLaws)
    → BiasedLaws (P // R) (SubstBiasedMgm SRel)
  unit-l (SubstBiasedLaws SRel SLaws) ((w , α) , r)=
    pair= (pair= (subst-unit-l w) (subst-unit-l-frm _ w α)) {!!}
  unit-r (SubstBiasedLaws SRel SLaws) = {!!}
  assoc (SubstBiasedLaws SRel SLaws) = {!!}
  unit-l-frm (SubstBiasedLaws SRel SLaws) = {!!}
  unit-r-frm (SubstBiasedLaws SRel SLaws) = {!!}
  assoc-frm (SubstBiasedLaws SRel SLaws) = {!!}


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
