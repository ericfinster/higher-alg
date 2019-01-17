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
    → (κ : (g : Ops P) → Node P w g → InFrame P g) 
    → InFrame P (i , f)
  subst-γ f w α κ = subst w κ , λ j → α j ∘e (subst-lf-eqv w κ j) ⁻¹

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
                → (κ : (g : Ops P) → Node P w g → InFrame P g) 
                → R (i , f) (subst-γ f w α κ)

  open SubstRel
  
  SubstBiasedMgm : SubstRel → BiasedMgm (P // R)
  η (SubstBiasedMgm SRel) (i , f) =
    subst-η f , η-rel SRel f
  η-frm (SubstBiasedMgm SRel) =
    subst-η-frm
  γ (SubstBiasedMgm SRel) {i , f} ((w , α) , r) κ =
    let κ' g n = fst (κ g n)
    in subst-γ f w α κ' , γ-rel SRel f w α r κ'
  γ-frm (SubstBiasedMgm SRel) ((w , α) , r) κ g =
    -- This might indicate that you have not chosen the
    -- most natural direction for the subst-nd equivalence...
    subst-nd-eqv  w (λ g n → fst (κ g n)) g

  --
  --  Substitution Laws
  --

  subst-unit-l : {i : I} (w : W P i)
    → subst w (λ g n → corolla P (snd g) , corolla-frm P (snd g)) == w
  subst-unit-l (lf i) = idp
  subst-unit-l (nd (f , ϕ)) = ap (λ x → nd (f , x))
    (Decor-== P (λ j p → subst-unit-l (ϕ j p)))

  postulate
  
    subst-unit-l-frm : {i : I} {f : Op P i}
      → (w : W P i) (α : Frame P w f)
      → (λ j → α j ∘e (subst-lf-eqv w (λ g n → subst-η (snd g)) j) ⁻¹)
          == α [ (λ x → Frame P x f) ↓ subst-unit-l w ]
    -- subst-unit-l-frm (lf i) α = λ= (λ j → equiv-== (λ _ → idp))
    -- subst-unit-l-frm (nd (f₀ , ϕ)) α =
    --   ↓-W-Frame-in P (λ j l₀ l₁ r → ap (–> (α j)) {!SubstRelMgm!})

    subst-unit-r-frm : {i : I} {f : Op P i}
      → (κ : (g : Ops P) → Node P (corolla P f) g → InFrame P g)
      → snd (κ (i , f) (inl idp))
          == (λ j → corolla-frm P f j ∘e (subst-lf-eqv (corolla P f) κ j) ⁻¹)
               [ (λ x → Frame P x f) ↓ graft-unit P (fst (κ (i , f) (inl idp))) ]
    -- subst-unit-r-frm {i} {f} κ =
    --   let ((w , α) , r) = κ (i , f) (inl idp)
    --   in  graft-unit-frm P w α ∙'ᵈ ↓-W-Frame-in P (λ { j l .l idp → {!!} }) 

  -- Substitution and grafting commute with each other
  subst-graft : {i : I} (w : W P i) (ψ : (j : I) → Leaf P w j → W P j)
    → (κ : (g : Ops P) → Node P w g → InFrame P g)
    → (θ : (g : Ops P) → Σ I (λ j → Σ (Leaf P w j) (λ l → Node P (ψ j l) g)) → InFrame P g) 
    → graft P (subst w κ) (λ j l → subst (ψ j (subst-lf-from w κ j l)) (λ g n → θ g (j , subst-lf-from w κ j l , n)))
      == subst (graft P w ψ) (λ g n → ⊔-rec (κ g) (θ g) (graft-node-from P w ψ g n))                          
  subst-graft (lf i) ψ κ θ = idp
  subst-graft (nd (f , ϕ)) ψ κ θ = 
    let (w , α) = κ (_ , f) (inl idp)
        p j l₀ = –> (α j) l₀
        ψ' j l₀ k l₁ = ψ k (j , p j l₀ , l₁)
        κ' j l₀ g n = κ g (inr (j , p j l₀ , n))
        θ' j l₀ g trpl = let (k , l₁ , n) = trpl in θ g (k , (j , p j l₀ , l₁) , n)
        ψ₀ j l₀ = subst (ϕ j (p j l₀)) (κ' j l₀)
        slf k j l₀ l₁ = subst-lf-from (ϕ j (p j l₀)) (κ' j l₀) k l₁
        ψ₁ k trpl = let (j , l₀ , l₁) = trpl in subst (ψ' j l₀ k (slf k j l₀ l₁)) (λ g n → θ' j l₀ g (k , slf k j l₀ l₁ , n))
    in graft P (graft P w ψ₀) (λ j l → ψ₁ j (graft-leaf-from P w ψ₀ j l))
         =⟨ graft-assoc P w ψ₀ ψ₁ ⟩
       graft P w (λ j l₀ → graft P (ψ₀ j l₀) (λ k l₁ → ψ₁ k (j , l₀ , l₁)))
         =⟨ ap (graft P w) (λ= (λ j → λ= (λ l₀ → subst-graft (ϕ j (p j l₀)) (ψ' j l₀) (κ' j l₀) (θ' j l₀) ∙
            ap (subst (graft P (ϕ j (p j l₀)) (ψ' j l₀))) (λ= (λ g → λ= (λ n →
              ⊔-rec-∘ (κ g) (θ g)
                  (λ l₁ → inr (j , p j l₀ , l₁))
                  (λ t → let (k , l₁ , n) = t in (k , (j , p j l₀ , l₁) , n))
                  (graft-node-from P (ϕ j (p j l₀)) (ψ' j l₀) g n))))))) ⟩ 
       subst (graft P (nd (f , ϕ)) ψ) (λ g n → ⊔-rec (κ g) (θ g) (graft-node-from P (nd (f , ϕ)) ψ g n)) ∎

  subst-assoc : {i : I} (w : W P i) 
    → (κ : (g : Ops P) → Node P w g → InFrame P g) 
    → (ν : (g : Ops P) → Σ (Ops P) (λ k → Σ (Node P w k) (λ p → Node P (fst (κ k p)) g)) → InFrame P g)
    → subst w (λ g n → subst-γ _ (fst (κ g n)) (snd (κ g n)) (λ g' n' → ν g' (g , n , n')))
      == subst (subst w κ) (λ g n → ν g (subst-nd-from w κ g n))
  subst-assoc (lf i) κ ν = idp
  subst-assoc (nd (f , ϕ)) κ ν = 
    let (w , α) = κ (_ , f) (inl idp)
        ν-here g n = ν g ((_ , f) , inl idp , n)
        κ' j p g n = κ g (inr (j , p , n))
        ν' j p g t = ν g (fst t , (inr (j , p , fst (snd t))) , snd (snd t))

        κ-left g n = subst-γ _ (fst (κ g n)) (snd (κ g n)) (λ g' n' → ν g' (g , n , n'))

        α-left j = α j ∘e (subst-lf-eqv w (λ g' n' → ν g' ((_ , f) , inl idp , n')) j) ⁻¹
        κ-left' j l g n = κ-left g (inr (j , –> (α-left j) l , n))
        ψ-left j l = subst (ϕ j (–> (α-left j) l)) (κ-left' j l)

        ψ-right j l = subst (ϕ j (–> (α j) l)) (κ' j (–> (α j) l))
        κ-right g n = ν g (subst-nd-from-lcl f ϕ κ g (graft-node-from P w ψ-right g n))

        
        ih j p = subst-assoc (ϕ j p) (κ' j p) (ν' j p)

        ψ-mid j l = subst (subst (ϕ j (–> (α-left j) l)) (κ' j (–> (α-left j) l)))
                          (λ g n → ν' j (–> (α-left j) l) g (subst-nd-from (ϕ j (–> (α-left j) l)) (κ' j (–> (α-left j) l)) g n))

        ψ-sg j l = subst (ϕ j (–> (α j) l)) (κ' j (–> (α j) l))
        θ g t = let (j , l , n) = t
                in ν' j (–> (α j) l) g (subst-nd-from (ϕ j (–> (α j) l)) (κ' j (–> (α j) l)) g n)

        test g t = let (j , l₀ , n) = t
                       (k , l₁ , n') = subst-nd-from (ϕ j (–> (α j) l₀)) (κ' j (–> (α j) l₀)) g n
                   in k , inr (j , –> (α j) l₀ , l₁) , n'

    in graft P (subst w ν-here) ψ-left 
         =⟨ λ= (λ j → λ= (λ l → ih j (–> (α-left j) l))) |in-ctx (λ x → graft P (subst w ν-here) x) ⟩
       graft P (subst w ν-here) (λ j l → subst (ψ-sg j (subst-lf-from w ν-here j l)) (λ g n → θ g (j , subst-lf-from w ν-here j l , n)))
         =⟨ subst-graft w ψ-sg ν-here θ ⟩
       subst (graft P w ψ-sg) (λ g n → ⊔-rec (ν-here g) (θ g) (graft-node-from P w ψ-sg g n))
         =⟨ λ= (λ g → λ= (λ n → ⊔-codiag (λ n → (_ , f) , inl idp , n) (test g) (ν g) (graft-node-from P w ψ-sg g n))) |in-ctx subst (graft P w ψ-sg) ⟩ 
       subst (graft P w ψ-sg) κ-right ∎

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
        → γ-rel SRel f w α r (λ g _ → fst (η (SubstBiasedMgm SRel) g))
            == r [ R (i , f) ↓ pair= (subst-unit-l w) (subst-unit-l-frm w α) ]

      subst-unit-r-rel : {i : I} {f : Op P i}
        → (κ : (g : Ops P) → Node P (corolla P f) g → Op (P // R) g)
        → snd (κ (i , f) (inl idp)) == γ-rel SRel f (corolla P f) (corolla-frm P f) (η-rel SRel f) (λ g n → fst (κ g n))
            [ R (i , f) ↓ pair= (graft-unit P (fst (fst ((κ (i , f) (inl idp)))))) (subst-unit-r-frm (λ g n → fst (κ g n))) ]

  open SubstRelLaws
  
  SubstBiasedLaws : (SRel : SubstRel) (SLaws : SubstRelLaws SRel)
    → BiasedLaws (P // R) (SubstBiasedMgm SRel)
  unit-l (SubstBiasedLaws SRel SLaws) ((w , α) , r) =
    pair= (pair= (subst-unit-l w) (subst-unit-l-frm w α))
          (subst-unit-l-rel SLaws w α r)
  unit-r (SubstBiasedLaws SRel SLaws) {i , f} κ =
    let ((w , α) , r) = κ (i , f) (inl idp)
    in pair= (pair= (graft-unit P w) (subst-unit-r-frm (λ g n → fst (κ g n))))
             (subst-unit-r-rel SLaws κ)
  assoc (SubstBiasedLaws SRel SLaws) ((w , α) , r) κ ν = {!!}
    -- pair= (pair= (subst-assoc w {!!} {!!}) {!!})
    --       {!!}
  unit-l-frm (SubstBiasedLaws SRel SLaws) ((w , α) , r) g n = {!!}
  unit-r-frm (SubstBiasedLaws SRel SLaws) κ g n = {!!}
  assoc-frm (SubstBiasedLaws SRel SLaws) = {!!}




