{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Grafting
open import Biased

module wip.SubstitutionLaws {ℓ} {I : Type ℓ} (P : Poly I) (R : PolyRel P) where

  open import Substitution P
  open import wip.SubstSubst P
  open BiasedMgm
  open BiasedLaws

  -- The extra information required from a relation in order that we
  -- can construct a biased multiplication on the slice by R.
  record SubstRel : Type ℓ where
    field

      η-rel : (f : Ops P) → R f (subst-η f)
        
      γ-rel : (f : Ops P) (wα : InFrame P f) (r : R f wα)
        → (κ : (g : Ops P) → Node P (fst wα) g → Op (P // R) g) 
        → R f (subst-γ f wα (λ g n → fst (κ g n)))

  open SubstRel
  
  SubstBiasedMgm : SubstRel → BiasedMgm (P // R)
  η (SubstBiasedMgm SRel) f =
    subst-η f , η-rel SRel f
  η-frm (SubstBiasedMgm SRel) =
    subst-η-frm
  γ (SubstBiasedMgm SRel) {f} (wα , r) κ =
    let κ' g n = fst (κ g n)
    in subst-γ f wα κ' , γ-rel SRel f wα r κ
  γ-frm (SubstBiasedMgm SRel) ((w , α) , r) κ g =
    let κ' g n = fst (κ g n)
    in subst-node-eqv w κ' g

  -- subst-assoc-frm : {i : I} {f : Op P i}
  --   → (w : W P i) (α : Frame P w f)
  --   → (κ : (g : Ops P) → Node P w g → InFrame P g)
  --   → (ν : (g : Ops P) → Σ (Ops P) (λ h → Σ (Node P w h) (λ n → Node P (fst (κ h n)) g)) → InFrame P g)
  --   → (λ j → α j ∘e subst-leaf-eqv w (λ g n → subst-γ g (κ g n) (λ g₁ n₁ → ν g₁ (g , n , n₁))) j ⁻¹) == 
  --     (λ j → (α j ∘e subst-leaf-eqv w κ j ⁻¹) ∘e subst-leaf-eqv (subst w κ) (λ g n → ν g (<– (subst-node-eqv w κ g) n)) j ⁻¹)
  --       [ (λ x → Frame P x f) ↓ subst-assoc w κ ν ]                          
  -- subst-assoc-frm w α κ ν =
  --   let κ' g n = subst-γ g (κ g n) (λ g₁ n₁ → ν g₁ (g , n , n₁))
  --       ν' g n = ν g (<– (subst-node-eqv w κ g) n)
  --       lem j l₀ l₁ q = subst-leaf-from w κ' j l₀
  --                         =⟨ ! (subst-lf-from-to {w = w} (subst-lf-from {w = w} {κ = κ'} l₀)) ⟩ 
  --                       subst-lf-from {w = w} {κ = κ} (subst-lf-to {w = w} {κ = κ} (subst-lf-from {w = w} {κ = κ'} l₀))
  --                         =⟨ ! (ap (subst-lf-from {w = w}) (subst-lf-from-to {w = subst w κ} (subst-lf-to {w = w} (subst-lf-from {w = w} l₀)))) ⟩
  --                       subst-lf-from {w = w} {κ = κ} (subst-lf-from {w = subst w κ} {κ = ν'}
  --                         (subst-lf-to {w = subst w κ} {κ = ν'} (subst-lf-to {w = w} {κ = κ} (subst-lf-from {w = w} {κ = κ'} l₀))))
  --                         =⟨ ! (to-transp (subst-assoc-lf-po w κ ν j (subst-lf-from {w = w} l₀)))
  --                           |in-ctx (λ x → subst-lf-from {w = w} (subst-lf-from {w = subst w κ} x)) ⟩ 
  --                       subst-lf-from {w = w} (subst-lf-from {w = subst w κ}
  --                         (transport (λ x → Leaf P x j) (subst-assoc w κ ν) (subst-lf-to (subst-lf-from {w = w} l₀)))) 
  --                         =⟨ subst-lf-to-from {w = w} l₀ |in-ctx (λ x → subst-lf-from {w = w} (subst-lf-from {w = subst w κ}
  --                              (transport (λ x → Leaf P x j) (subst-assoc w κ ν) x))) ⟩ 
  --                       subst-lf-from {w = w} (subst-lf-from {w = subst w κ} (transport (λ x → Leaf P x j) (subst-assoc w κ ν) l₀)) 
  --                         =⟨ to-transp q |in-ctx (λ x → subst-lf-from {w = w} (subst-lf-from {w = subst w κ} x)) ⟩ 
  --                       subst-lf-from {w = w} (subst-lf-from {w = subst w κ} l₁) ∎
  --   in ↓-W-Frame-in P (λ j l₀ l₁ q → ap (–> (α j)) (lem j l₀ l₁ q)) 

  -- postulate
  
  --   subst-node-assoc : {i : I} {f : Op P i}
  --     → (w : W P i) (α : Frame P w f)
  --     → (κ : (g : Ops P) → Node P w g → InFrame P g)
  --     → (ν : (g : Ops P) → Σ (Ops P) (λ h → Σ (Node P w h) (λ n → Node P (fst (κ h n)) g)) → InFrame P g)
  --     → (g h : Ops P) (m : Node P w h) (k : Ops P) (n : Node P (fst (κ h m)) k) (o : Node P (fst (ν k (h , m , n))) g)
  --     → subst-node-to w (λ g₁ n₁ → subst-γ g₁ (κ g₁ n₁) (λ g' n' → ν g' (g₁ , n₁ , n')))
  --                   g (h , m , subst-node-to (fst (κ h m)) (λ g' n' → ν g' (h , m , n')) g (k , n , o))
  --         == subst-node-to (subst w κ) (λ g₁ n₁ → ν g₁ (subst-node-from w κ g₁ n₁))
  --              g (k , subst-node-to w κ k (h , m , n) , transport! (λ x → Node P (fst (ν k x)) g) (<–-inv-l (subst-node-eqv w κ k) (h , m , n)) o)
  --           [ (λ x → Node P x g) ↓ subst-assoc w κ ν ]
  --   -- subst-node-assoc = {!!}

  -- record SubstRelLaws (SRel : SubstRel) : Type ℓ where
  --   field

  --     subst-unit-l-rel : {i : I} {f : Op P i}
  --       → (w : W P i) (α : Frame P w f) (r : R (i , f) (w , α))
  --       → γ-rel SRel (i , f) (w , α) r (λ g _ → η (SubstBiasedMgm SRel) g)
  --           == r [ R (i , f) ↓ pair= (subst-unit-l w) (subst-unit-l-frm w α) ]

  --     subst-unit-r-rel : {i : I} {f : Op P i}
  --       → (κ : (g : Ops P) → Node P (corolla P f) g → Op (P // R) g)
  --       → snd (κ (i , f) (inl idp)) == γ-rel SRel (i , f) (corolla P f , corolla-frm P f) (η-rel SRel (i , f)) κ
  --           [ R (i , f) ↓ pair= (graft-unit P (fst (fst ((κ (i , f) (inl idp)))))) (subst-unit-r-frm (λ g n → fst (κ g n))) ]

  --     subst-assoc-rel : {i : I} {f : Op P i}
  --       → (w : W P i) (α : Frame P w f) (r : R (i , f) (w , α))
  --       → (κ : (g : Ops P) → Node P w g → Op (P // R) g)
  --       → (ν : (g : Ops P) → Σ (Ops P) (λ h → Σ (Node P w h) (λ n → Node P (fst (fst (κ h n))) g)) → Op (P // R) g)
  --       → let κ' g n = fst (κ g n)
  --             ν' g t = fst (ν g t)
  --         in γ-rel SRel (i , f) (w , α) r (λ g n → subst-γ g (κ' g n) (λ g₁ n₁ → ν' g₁ (g , n , n₁)) ,
  --                                                  γ-rel SRel g (κ' g n) (snd (κ g n)) (λ g₁ n₁ → ν g₁ (g , n , n₁)))
  --            == γ-rel SRel (i , f) (subst-γ (i , f) (w , α) κ')
  --                                  (γ-rel SRel (i , f) (w , α) r κ)
  --                                  (λ g n → ν g (<– (subst-node-eqv w κ' g) n))
  --              [ R (i , f) ↓ pair= (subst-assoc w κ' ν') (subst-assoc-frm w α κ' ν') ]


  -- open SubstRelLaws

  -- SubstBiasedLaws : (SRel : SubstRel) (SLaws : SubstRelLaws SRel)
  --   → BiasedLaws (P // R) (SubstBiasedMgm SRel)
  -- unit-l (SubstBiasedLaws SRel SLaws) ((w , α) , r) =
  --   pair= (pair= (subst-unit-l w) (subst-unit-l-frm w α))
  --         (subst-unit-l-rel SLaws w α r)
  -- unit-r (SubstBiasedLaws SRel SLaws) {i , f} κ =
  --   let ((w , α) , r) = κ (i , f) (inl idp)
  --       κ' g n = fst (κ g n)
  --   in pair= (pair= (graft-unit P w) (subst-unit-r-frm κ'))
  --            (subst-unit-r-rel SLaws κ)
  -- assoc (SubstBiasedLaws SRel SLaws) {i , f} ((w , α) , r) κ ν = 
  --   let κ' g n = fst (κ g n)
  --       ν' g t = fst (ν g t)
  --   in pair= (pair= (subst-assoc w κ' ν') (subst-assoc-frm w α κ' ν'))
  --            (subst-assoc-rel SLaws w α r κ ν)
  -- unit-l-frm (SubstBiasedLaws SRel SLaws) ((w , α) , r) g n =
  --   ↓-Σ-weaken (λ x → Node P (fst x) g)
  --     (↓-Σ-weaken (λ x → Node P x g)
  --                 (subst-node-unit-l w g n))
  -- unit-r-frm (SubstBiasedLaws SRel SLaws) {i , f} κ g n =
  --   ↓-Σ-weaken (λ x → Node P (fst x) g)
  --     (↓-Σ-weaken (λ x → Node P x g)
  --       (graft-unit-nd P (fst (fst (κ (_ , f) (inl idp)))) g n)) 
  -- assoc-frm (SubstBiasedLaws SRel SLaws) ((w , α) , r) κ ν g h m k n o =
  --   let κ' g n = fst (κ g n)
  --       ν' g t = fst (ν g t)
  --   in ↓-Σ-weaken (λ x → Node P (fst x) g)
  --        (↓-Σ-weaken (λ x → Node P x g)
  --                    (subst-node-assoc w α κ' ν' g h m k n o))

