{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial

-- Proving that substitution is associative
module wip.SubstSubst {ℓ} {I : Type ℓ} (P : Poly I) where

  open import Grafting P
  open import Substitution P
  open import wip.SubstGraft P

  -- subst-γ : (f : Ops P) (wα : InFrame P f)
  --   → (κ : (g : Ops P) → Node P (fst wα) g → InFrame P g) 
  --   → InFrame P f
  -- subst-γ (i , f) (w , α) κ =
  --   subst w κ , λ j → α j ∘e (subst-leaf-eqv w κ j) ⁻¹

  subst-frm-∘ : {i : I} {f : Op P i} {w : W P i}
    → (α : Frame P w f)
    → (κ : (g : Ops P) → Node P w g → InFrame P g)
    → Frame P (subst w κ) f
  subst-frm-∘ α κ j = α j ∘e (subst-leaf-eqv _ κ j)⁻¹

  -- module SSLocal {i : I} (f : Op P i) (ϕ : Decor P f (W P)) 
  --   (κ : (g : Ops P) → Node P (nd (f , ϕ)) g → InFrame P g) 
  --   (ν : (g : Ops P) → Σ (Ops P) (λ k → Σ (Node P (nd (f , ϕ)) k) (λ p → Node P (fst (κ k p)) g)) → InFrame P g) where

  --   w = fst (κ (_ , f) (inl idp))
  --   α = snd (κ (_ , f) (inl idp))

  --   -- induction hypothesis
  --   κ' = λ j p g n → κ g (inr (j , p , n))
  --   ν' = λ j p g t → ν g (fst t , (inr (j , p , fst (snd t))) , snd (snd t))
  --   β = λ j → α j ∘e (subst-leaf-eqv w (λ g n → ν g ((i , f) , inl idp , n)) j) ⁻¹

  --   -- arguments for subst-graft
  --   κ-sg = λ g n → ν g ((_ , f) , inl idp , n)
  --   ψ-sg = λ j l → subst (ϕ j (–> (α j) l)) (κ' j (–> (α j) l))
  --   θ-sg = λ g t → let (j , l , n) = t
  --                  in ν' j (–> (α j) l) g (subst-node-from (ϕ j (–> (α j) l)) (κ' j (–> (α j) l)) g n)

  --   -- Decoration fixup ...
  --   θ' = λ g t → let (j , l₀ , n) = t
  --                    (k , l₁ , n') = subst-node-from (ϕ j (–> (α j) l₀)) (κ' j (–> (α j) l₀)) g n
  --                in k , inr (j , –> (α j) l₀ , l₁) , n'

  --
  --  Associativity of substitution
  -- 

  subst-assoc : {i : I} (w : W P i) 
    → (κ : (g : Ops P) → Node P w g → InFrame P g) 
    → (ν : (g : Ops P) → Σ (Ops P) (λ k → Σ (Node P w k) (λ p → Node P (fst (κ k p)) g)) → InFrame P g)
    → subst w (λ g n → subst (fst (κ g n)) (λ h m → ν h (g , n , m)) , subst-frm-∘ (snd (κ g n)) (λ h m → ν h (g , n , m)))
      == subst (subst w κ) (λ g n → ν g (subst-node-from w κ g n))
  subst-assoc (lf i) κ ν = idp
  subst-assoc (nd (f , ϕ)) κ ν = 
    let -- open SSLocal f ϕ κ ν

        w = fst (κ (_ , f) (inl idp))
        α = snd (κ (_ , f) (inl idp))

        -- induction hypothesis
        κ' = λ j p g n → κ g (inr (j , p , n))
        ν' = λ j p g t → ν g (fst t , (inr (j , p , fst (snd t))) , snd (snd t))
        β = λ j → α j ∘e (subst-leaf-eqv w (λ g n → ν g ((_ , f) , inl idp , n)) j) ⁻¹

        -- arguments for subst-graft
        κ-sg = λ g n → ν g ((_ , f) , inl idp , n)
        ψ-sg = λ j l → subst (ϕ j (–> (α j) l)) (κ' j (–> (α j) l))
        θ-sg = λ g t → let (j , l , n) = t
                       in ν' j (–> (α j) l) g (subst-node-from (ϕ j (–> (α j) l)) (κ' j (–> (α j) l)) g n)

        -- Decoration fixup ...
        θ' = λ g t → let (j , l₀ , n) = t
                         (k , l₁ , n') = subst-node-from (ϕ j (–> (α j) l₀)) (κ' j (–> (α j) l₀)) g n
                     in k , inr (j , –> (α j) l₀ , l₁) , n'

        ζ g n = ν g (subst-node-from (nd (f , ϕ)) κ g n)
        ζ' j p g n = ν' j p g (subst-node-from (ϕ j p) (κ' j p) g n)

        ζ-lem : (j : I) (p : Param P f j) (g : Ops P) (n : Node P (subst (ϕ j p) (κ' j p)) g)
          → ζ' j p g n == ζ g (graft-node-to w ψ-sg g (inr (j , <– (α j) p , {!n!})))
        ζ-lem j p g n = {!!}

        ih j p = subst-assoc (ϕ j p) (κ' j p) (ν' j p) 
        lem g n = ⊔-codiag (λ n → (_ , f) , inl idp , n) (θ' g) (ν g) (graft-node-from w ψ-sg g n)
        
    in ap (graft (subst w κ-sg)) (Decor-== (Fr P) (λ j l → ih j (–> (β j) l))) ∙ 
       subst-graft w ψ-sg κ-sg θ-sg ∙
       ap (subst (graft w ψ-sg)) (λ= (λ g → λ= (λ n → {!!})))

  -- postulate
  
  --   subst-assoc-lf-po : {i : I} (w : W P i) 
  --     → (κ : (g : Ops P) → Node P w g → InFrame P g)
  --     → (ν : (g : Ops P) → Σ (Ops P) (λ h → Σ (Node P w h) (λ n → Node P (fst (κ h n)) g)) → InFrame P g)
  --     → (j : I) (l : Leaf P w j)
  --     → subst-lf-to {w = w} l == subst-lf-to {w = subst w κ} (subst-lf-to {w = w} l) [ (λ x → Leaf P x j) ↓ subst-assoc w κ ν ] 
  --   -- subst-assoc-lf-po (lf i) κ ν .i idp = idp
  --   -- subst-assoc-lf-po (nd (f , ϕ)) κ ν j (k , p , l) = 
  --   --   let (w , α) = κ (_ , f) (inl idp)

  --   --       -- induction hypothesis
  --   --       κ' j p g n = κ g (inr (j , p , n))
  --   --       ν' j p g t = ν g (fst t , (inr (j , p , fst (snd t))) , snd (snd t))
  --   --       α' j = α j ∘e (subst-leaf-eqv w (λ g' n' → ν g' ((_ , f) , inl idp , n')) j) ⁻¹
  --   --       ih j p = subst-assoc (ϕ j p) (κ' j p) (ν' j p) 

  --   --       -- arguments for subst-graft
  --   --       κ-sg g n = ν g ((_ , f) , inl idp , n)
  --   --       ψ-sg j l = subst (ϕ j (–> (α j) l)) (κ' j (–> (α j) l))

  --   --       ih-po : subst-lf-to l == subst-lf-to (subst-lf-to l) [ (λ x → Leaf P x j) ↓ subst-assoc (ϕ k p) (κ' k p) (ν' k p) ]
  --   --       ih-po = subst-assoc-lf-po (ϕ k p) (κ' k p) (ν' k p) j l

  --   --       my-κ g n = subst-γ _ (κ g n) (λ g' n' → ν g' (g , n , n'))
  --   --       my-ν g n = ν g (subst-node-from (nd (f , ϕ)) κ g n)
  --   --       pth₀ = ap (graft P (subst w κ-sg)) (Decor-== (Fr P) (λ j l → ih j (–> (α' j) l)))

  --   --       Q x =  Leaf P (subst (ϕ k x) (λ g n → my-κ g (inr (k , x , n)))) j 
  --   --       Q' x = Leaf P (subst (subst (ϕ k x) (κ' k x)) (λ g n → ν' k x g (subst-node-from (ϕ k x) (κ' k x) g n))) j 

  --   --       l' = <– (α' k) p
  --   --       p' = –> (α' k) l'
  --   --       l₀ = transport! Q (<–-inv-r (α' k) p) (subst-lf-to {w = ϕ k p} l)
  --   --       l₁ = transport! Q' (<–-inv-r (α' k) p) (subst-lf-to {w = subst (ϕ k p) (κ' k p)} (subst-lf-to {w = ϕ k p} l))

  --   --       pth-ovr₀ : graft-lf-to P {w = subst w κ-sg} (k , l' , l₀)
  --   --         == graft-lf-to P {w = subst w κ-sg} (k , l' , l₁)
  --   --           [ (λ x → Leaf P (graft P (subst w κ-sg) x) j) ↓ Decor-== (Fr P) (λ j l → ih j (–> (α' j) l)) ]
  --   --       pth-ovr₀ = ↓-graft-Leaf-ih P (λ j₁ l₁ → ih j₁ (–> (α' j₁) l₁)) k l' {!!}

  --   --       pth-ovr₁ : graft-lf-to P {w = subst w κ-sg} (k , l' , l₀)
  --   --         == graft-lf-to P {w = subst w κ-sg} (k , l' , l₁) [ (λ x → Leaf P x j) ↓ pth₀ ]
  --   --       pth-ovr₁ = ↓-ap-in (λ x → Leaf P x j) (graft P (subst w κ-sg)) pth-ovr₀ 

  --   --   in pth-ovr₁ ∙ᵈ {!!}

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
