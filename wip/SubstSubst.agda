{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial

-- Proving that substitution is associative
module wip.SubstSubst {ℓ} {I : Type ℓ} (P : Poly I) where

  open import Grafting P
  open import Substitution P
  open import wip.SubstGraft P

  subst-frm-∘ : {i : I} {f : Op P i} {w : W P i}
    → (α : Frame P w f)
    → (κ : (g : Ops P) → Node P w g → InFrame P g)
    → Frame P (subst w κ) f
  subst-frm-∘ α κ j = α j ∘e (subst-leaf-eqv _ κ j)⁻¹

  SADecor : {i : I} (w : W P i) (κ : SubstDecor w) → Type ℓ
  SADecor w κ = (g : Ops P)
    → Σ (Ops P) (λ k → Σ (Node P w k) (λ p → Node P (fst (κ k p)) g))
    → InFrame P g

  subst-assoc-decor-left : {i : I} (w : W P i) 
    → (κ : SubstDecor w) (ν : SADecor w κ)
    → SubstDecor w
  subst-assoc-decor-left w κ ν g n = 
    subst (fst (κ g n)) (λ h m → ν h (g , n , m)) ,
    subst-frm-∘ (snd (κ g n)) (λ h m → ν h (g , n , m))

  subst-assoc-decor-right : {i : I} (w : W P i) 
    → (κ : SubstDecor w) (ν : SADecor w κ)
    → SubstDecor (subst w κ)
  subst-assoc-decor-right w κ ν g n =
    ν g (subst-node-from w κ g n)

  module SSLocal {i : I} (f : Op P i) (ϕ : Decor P f (W P))
    (κ : SubstDecor (nd (f , ϕ))) (ν : SADecor (nd (f , ϕ)) κ) where

      w = fst (κ (_ , f) (inl idp))
      α = snd (κ (_ , f) (inl idp))

      -- β : Frame P (subst (nd (f , ϕ)) κ) f
      -- β = subst-frm-∘ α (λ g n → ν g ((_ , f) , inl idp , n))

      -- ih decorations
      κ' : (j : I) (p : Param P f j) → SubstDecor (ϕ j p)
      κ' j p g n = κ g (inr (j , p , n))

      ν' : (j : I) (p : Param P f j) → SADecor (ϕ j p) (κ' j p)
      ν' j p g t = ν g (fst t , (inr (j , p , fst (snd t))) , snd (snd t))

      -- subst-graft decorations
      ψ-sg : Decor (Fr P) w (W P)
      ψ-sg j l = subst (ϕ j (–> (α j) l)) (κ' j (–> (α j) l))

      κ-sg : SubstDecor w
      κ-sg g n = ν g ((_ , f) , inl idp , n)

      nd-split : (g : Ops P)
        → Σ I (λ j → Σ (Leaf P w j) (λ l → Node P (ψ-sg j l) g))
        → Σ (Ops P) (λ h → Σ (Node P (nd (f , ϕ)) h) (λ n → Node P (fst (κ h n)) g))
      nd-split g (j₀ , l₀ , n₀) =
        let p₀ = –> (α j₀) l₀
            (j₁ , l₁ , n₁) = subst-node-from (ϕ j₀ p₀) (κ' j₀ p₀) g n₀
        in j₁ , inr (j₀ , p₀ , l₁) , n₁

      θ-sg : SGDecor ψ-sg κ-sg
      θ-sg g t = ν g (nd-split g t)

      -- ih decoration fixup
      sa-decor-lem : (g : Ops P) (n : Node P (graft w ψ-sg) g)
        → subst-graft-decor-right w ψ-sg κ-sg θ-sg g n
          == subst-assoc-decor-right (nd (f , ϕ)) κ ν g n
      sa-decor-lem g n = ⊔-codiag (λ n → (_ , f) , inl idp , n)
        (nd-split g) (ν g) (graft-node-from w ψ-sg g n)

  --
  --  Associativity of substitution
  -- 

  subst-assoc : {i : I} (w : W P i) 
    → (κ : SubstDecor w) (ν : SADecor w κ)
    → subst w (subst-assoc-decor-left w κ ν)
      == subst (subst w κ) (subst-assoc-decor-right w κ ν)
  subst-assoc (lf i) κ ν = idp
  subst-assoc (nd (f , ϕ)) κ ν = 
    let open SSLocal f ϕ κ ν

        β = subst-frm-∘ α (λ g n → ν g ((_ , f) , inl idp , n))
        ih j p = subst-assoc (ϕ j p) (κ' j p) (ν' j p)

    in ap (graft (subst w κ-sg)) (Decor-== (Fr P) (λ j l → ih j (–> (β j) l))) ∙ 
       subst-graft w ψ-sg κ-sg θ-sg ∙
       ap (subst (graft w ψ-sg)) (λ= (λ g → λ= (λ n → sa-decor-lem g n)))

  subst-assoc-leaf-to-left : {i : I} (w : W P i) 
    → (κ : SubstDecor w) (ν : SADecor w κ)
    → (j : I) (l : Leaf P w j)
    → Leaf P (subst w (subst-assoc-decor-left w κ ν)) j
  subst-assoc-leaf-to-left w κ ν j l =
    subst-lf-to {w = w} l

  subst-assoc-leaf-to-right : {i : I} (w : W P i) 
    → (κ : SubstDecor w) (ν : SADecor w κ)
    → (j : I) (l : Leaf P w j)
    → Leaf P (subst (subst w κ) (subst-assoc-decor-right w κ ν)) j
  subst-assoc-leaf-to-right w κ ν j l = 
    subst-lf-to {w = subst w κ} (subst-lf-to {w = w} l)

  postulate
  
    subst-assoc-lf-ovr : {i : I} (w : W P i) 
      → (κ : SubstDecor w) (ν : SADecor w κ)
      → (j : I) (l : Leaf P w j)
      → subst-lf-to {w = w} l == subst-lf-to {w = subst w κ} (subst-lf-to {w = w} l)
          [ (λ x → Leaf P x j) ↓ subst-assoc w κ ν ] 
    -- subst-assoc-lf-ovr (lf i) κ ν .i idp = idp
    -- subst-assoc-lf-ovr (nd (f , ϕ)) κ ν j (k , p , l) = 
    --   let open SSLocal f ϕ κ ν

    --       l' = <– (α k) p
    --       p' = –> (α k) l'
    --       l₀ = transport! (λ x → Leaf P (ϕ k x) j) (<–-inv-r (α k) p) l

    --       β = subst-frm-∘ α (λ g n → ν g ((_ , f) , inl idp , n))
    --       ih j p = subst-assoc (ϕ j p) (κ' j p) (ν' j p)

    --       βp = –> (β k) (subst-lf-to (<– (α k) p))
    --       βp=p = βp =⟨ {!!} ⟩ p ∎
    --       βl = transport! (λ x → Leaf P (ϕ k x) j) βp=p l

    --       lem₀ = subst-leaf-to (ϕ k (–> (β k)(<– (β k) p)))
    --                            (λ g n → subst-assoc-decor-left (nd (f , ϕ)) κ ν g (inr (k , –> (β k) (<– (β k) p) , n))) j
    --                            (transport! (λ x → Leaf P (ϕ k x) j) (<–-inv-r (β k) p) l)
    --                =⟨ {!!} ⟩
    --              subst-assoc-leaf-to-left (ϕ k βp) (κ' k βp) (ν' k βp) j βl ∎

    --       lem₁ = subst-assoc-leaf-to-right (ϕ k βp) (κ' k βp) (ν' k βp) j βl
    --                =⟨ {!idp!} ⟩ 
    --              subst-lf-to (transport! (λ x → Leaf P (ψ-sg k x) j)
    --                          (subst-leaf-from-to w κ-sg k l')
    --                          (subst-lf-to l₀)) ∎

    --       ih-po : subst-assoc-leaf-to-left (nd (f , ϕ)) κ ν j (k , p , l) ==
    --               subst-graft-leaf-to-left w ψ-sg κ-sg θ-sg j k l' (subst-lf-to {w = ϕ k p'} l₀)
    --                 [ (λ x → Leaf P x j) ↓ ap (graft (subst w κ-sg)) (Decor-== (Fr P) (λ j l → ih j (–> (β j) l))) ]
    --       ih-po = ↓-ap-in (λ x → Leaf P x j) (graft (subst w κ-sg))
    --                 (↓-graft-Leaf-ih (λ j₁ l₁ → ih j₁ (–> (β j₁) l₁)) k (subst-lf-to {w = w} l')
    --                                  (lem₀ ∙ᵈ subst-assoc-lf-ovr (ϕ k βp) (κ' k βp) (ν' k βp) j βl ∙'ᵈ lem₁))

    --       sg-po : subst-graft-leaf-to-left w ψ-sg κ-sg θ-sg j k l' (subst-lf-to {w = ϕ k p'} l₀) ==
    --               subst-graft-leaf-to-right w ψ-sg κ-sg θ-sg j k l' (subst-lf-to {w = ϕ k p'} l₀)
    --                 [ (λ x → Leaf P x j) ↓ subst-graft w ψ-sg κ-sg θ-sg ]
    --       sg-po = subst-graft-lf-ovr w ψ-sg κ-sg θ-sg j k (<– (α k) p) (subst-lf-to {w = ϕ k p'} l₀)

    --       last-po : subst-graft-leaf-to-right w ψ-sg κ-sg θ-sg j k l' (subst-lf-to {w = ϕ k p'} l₀) ==
    --                 subst-assoc-leaf-to-right (nd (f , ϕ)) κ ν j (k , p , l)
    --                   [ (λ x → Leaf P x j) ↓ ap (subst (graft w ψ-sg)) (λ= (λ g → λ= (λ n → sa-decor-lem g n))) ]
    --       last-po = ↓-ap-in (λ x → Leaf P x j) (subst (graft w ψ-sg))
    --                         (↓-subst-Leaf-ih sa-decor-lem idp)

    --   in ih-po ∙ᵈ sg-po ∙ᵈ last-po  

  subst-assoc-node-to-left : {i : I} (w : W P i) 
    → (κ : SubstDecor w) (ν : SADecor w κ)
    → (g h k : Ops P) (m : Node P w g) (n : Node P (fst (κ g m)) h) (o : Node P (fst (ν h (g , m , n))) k)
    → Node P (subst w (subst-assoc-decor-left w κ ν)) k
  subst-assoc-node-to-left w κ ν g h k m n o =
    subst-nd-to {w = w} (g , m , subst-nd-to {w = fst (κ g m)} (h , n , o))

  subst-assoc-node-to-right : {i : I} (w : W P i) 
    → (κ : SubstDecor w) (ν : SADecor w κ)
    → (g h k : Ops P) (m : Node P w g) (n : Node P (fst (κ g m)) h) (o : Node P (fst (ν h (g , m , n))) k)
    → Node P (subst (subst w κ) (subst-assoc-decor-right w κ ν)) k
  subst-assoc-node-to-right w κ ν g h k m n o =
    subst-nd-to {w = subst w κ} (h , subst-nd-to {w = w} (g , m , n) ,
      transport! (λ x → Node P (fst (ν h x)) k) (<–-inv-l (subst-node-eqv w κ h) (g , m , n)) o)

  postulate
  
    subst-node-assoc : {i : I} (w : W P i) 
      → (κ : SubstDecor w) (ν : SADecor w κ)
      → (g h k : Ops P) (m : Node P w g) (n : Node P (fst (κ g m)) h) (o : Node P (fst (ν h (g , m , n))) k)
      → subst-assoc-node-to-left w κ ν g h k m n o ==
        subst-assoc-node-to-right w κ ν g h k m n o [ (λ x → Node P x k) ↓ subst-assoc w κ ν ]
    
