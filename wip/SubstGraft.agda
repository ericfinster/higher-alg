{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Grafting

-- Proving that substitution and grafting commute with each other
module wip.SubstGraft {ℓ} {I : Type ℓ} (P : Poly I) where

  open import Substitution P

  subst-graft : {i : I} (w : W P i) (ψ : (j : I) → Leaf P w j → W P j)
    → (κ : (g : Ops P) → Node P w g → InFrame P g)
    → (θ : (g : Ops P) → Σ I (λ j → Σ (Leaf P w j) (λ l → Node P (ψ j l) g)) → InFrame P g) 
    → graft P (subst w κ) (λ j l → subst (ψ j (subst-leaf-from w κ j l)) (λ g n → θ g (j , subst-leaf-from w κ j l , n)))
      == subst (graft P w ψ) (λ g n → ⊔-rec (κ g) (θ g) (graft-node-from P w ψ g n))                          
  subst-graft (lf i) ψ κ θ = idp
  subst-graft (nd (f , ϕ)) ψ κ θ = 
    let (w , α) = κ (_ , f) (inl idp)

        ψ' j p k l = ψ k (j , p , l)
        κ' j p g n = κ g (inr (j , p , n))
        θ' j p g t = let (k , l , n) = t in θ g (k , (j , p , l) , n)
        ih j p = subst-graft (ϕ j p) (ψ' j p) (κ' j p) (θ' j p)

        -- double graft arguments
        ψ₀ j l = subst (ϕ j (–> (α j) l)) (κ' j (–> (α j) l))
        ψ₁ k t = let (j , l₀ , l₁) = t
                     p = –> (α j) l₀
                     lϕ = subst-leaf-from (ϕ j p) (κ' j p) k l₁
                 in subst (ψ' j p k lϕ) (λ g n → θ' j p g (k , lϕ , n))

        -- fixup lemma
        lem j l₀ g n = ⊔-rec-∘ (κ g) (θ g)
                              (λ l₁ → inr (j , –> (α j) l₀ , l₁))
                              (λ t → let (k , l₁ , n) = t in (k , (j , –> (α j) l₀ , l₁) , n))
                              (graft-node-from P (ϕ j (–> (α j) l₀)) (ψ' j (–> (α j) l₀)) g n)

        -- Decoration equality
        H j l = ih j (–> (α j) l) ∙ ap (subst (graft P (ϕ j (–> (α j) l)) (ψ' j (–> (α j) l))))
                                       (λ= (λ g → λ= (λ n → lem j l g n)))

    in graft-assoc P w ψ₀ ψ₁ ∙
       ap (graft P w) (Decor-== (Fr P) H)

  subst-graft-nd-left : {i : I} (w : W P i) (ψ : (j : I) → Leaf P w j → W P j)
    → (κ : (g : Ops P) → Node P w g → InFrame P g)
    → (θ : (g : Ops P) → Σ I (λ j → Σ (Leaf P w j) (λ l → Node P (ψ j l) g)) → InFrame P g)
    → (g : Ops P) (h : Ops P) (m : Node P w g) (n : Node P (fst (κ g m)) h)
    → graft-node-to P (subst w κ) _ h (inl (subst-nd-to {w = w} (g , m , n))) ==
      subst-nd-to {w = graft P w ψ} (g , graft-nd-to P (inl m) ,
        transport! (λ x → Node P (fst (⊔-rec (κ g) (θ g) x)) h) (graft-nd-from-to P (inl m)) n)
          [ (λ x → Node P x h) ↓ subst-graft w ψ κ θ ]
  subst-graft-nd-left = {!!}

  subst-graft-nd-right : {i : I} (w : W P i) (ψ : (j : I) → Leaf P w j → W P j)
    → (κ : (g : Ops P) → Node P w g → InFrame P g)
    → (θ : (g : Ops P) → Σ I (λ j → Σ (Leaf P w j) (λ l → Node P (ψ j l) g)) → InFrame P g)
    → (j : I) (l : Leaf P w j) (g : Ops P) (h : Ops P) (m : Node P (ψ j l) g) (n : Node P (fst (θ g (j , l , m))) h)
    → graft-node-to P (subst w κ) _ h (inr (j , subst-lf-to {w = w} l ,
        (transport!
           (λ x → Node P (subst (ψ j x) (λ g₁ n₁ → θ g₁ (j , x , n₁))) h)
           (subst-leaf-from-to w κ j l) (subst-nd-to {w = ψ j l} (g , m , n))))) ==
      subst-nd-to {w = graft P w ψ} (g , graft-nd-to P (inr (j , l , m)) ,
        transport! (λ x → Node P (fst (⊔-rec (κ g) (θ g) x)) h) (graft-nd-from-to P (inr (j , l , m))) n)
          [ (λ x → Node P x h) ↓ subst-graft w ψ κ θ ]
  subst-graft-nd-right = {!!}

  --
  -- Induced action on leaves
  -- 

  -- subst-graft-lf-ovr : {i : I} (w : W P i) (ψ : (j : I) → Leaf P w j → W P j)
  --   → (κ : (g : Ops P) → Node P w g → InFrame P g)
  --   → (θ : (g : Ops P) → Σ I (λ j → Σ (Leaf P w j) (λ l → Node P (ψ j l) g)) → InFrame P g)
  --   → (j : I) (k : I) (l₀ : Leaf P w k) (l₁ : Leaf P (ψ k l₀) j)
  --   → graft-lf-to P {w = subst w κ} (k , subst-lf-to {w = w} l₀ ,
  --       subst-lf-to {w = ψ k (subst-leaf-from w κ k (subst-lf-to l₀))}
  --         (transport! (λ x → Leaf P (ψ k x) j) (subst-leaf-from-to w κ k l₀) l₁))
  --     == subst-lf-to {w = graft P w ψ} (graft-lf-to P {w = w} (k , l₀ , l₁)) [ (λ x → Leaf P x j) ↓ subst-graft w ψ κ θ ]
  -- subst-graft-lf-ovr (lf i) ψ κ θ j .i idp l₁ = idp
  -- subst-graft-lf-ovr (nd (f , ϕ)) ψ κ θ j k (k₀ , p₀ , l₀) l₁ = 
  --   let (w , α) = κ (_ , f) (inl idp)

  --       ψ' j p k l = ψ k (j , p , l)
  --       κ' j p g n = κ g (inr (j , p , n))
  --       θ' j p g t = let (k , l , n) = t in θ g (k , (j , p , l) , n)
  --       ih-pth j p = subst-graft (ϕ j p) (ψ' j p) (κ' j p) (θ' j p)

  --       -- double graft arguments
  --       ψ₀ j l = subst (ϕ j (–> (α j) l)) (κ' j (–> (α j) l))
  --       ψ₁ k t = let (j , l₀ , l₁) = t
  --                    p = –> (α j) l₀
  --                    lϕ = subst-leaf-from (ϕ j p) (κ' j p) k l₁
  --                in subst (ψ' j p k lϕ) (λ g n → θ' j p g (k , lϕ , n))

  --       -- fixup lemma
  --       lem j l₀ g n = ⊔-rec-∘ (κ g) (θ g)
  --                             (λ l₁ → inr (j , –> (α j) l₀ , l₁))
  --                             (λ t → let (k , l₁ , n) = t in (k , (j , –> (α j) l₀ , l₁) , n))
  --                             (graft-node-from P (ϕ j (–> (α j) l₀)) (ψ' j (–> (α j) l₀)) g n)

  --       -- Decoration equality
  --       H j l = ih-pth j (–> (α j) l) ∙ ap (subst (graft P (ϕ j (–> (α j) l)) (ψ' j (–> (α j) l))))
  --                                      (λ= (λ g → λ= (λ n → lem j l g n)))

  --       -- Various Transports and lemmas ...
  --       lf₀ = <– (α k₀) p₀

  --       p₀' = –> (α k₀) lf₀
  --       l₀' = transport! (λ x → Leaf P (ϕ k₀ x) k) (<–-inv-r (α k₀) p₀) l₀
  --       l₁' = transport! (λ x → Leaf P (ψ k (k₀ , x)) j)
  --                        (transp!-pair-lem (λ x → Leaf P (ϕ k₀ x) k) (α k₀) p₀ l₀) l₁


  --       lf₁ = subst-lf-to {w = ϕ k₀ p₀'} l₀'
  --       lf₂ = subst-lf-to {w = ψ k (k₀ , p₀' , subst-leaf-from (ϕ k₀ p₀') (κ' k₀ p₀') k lf₁)}
  --               (transport! (λ x → Leaf P (ψ k (k₀ , p₀' , x)) j)
  --                           (subst-lf-from-to {w = ϕ k₀ p₀'} l₀') l₁') 

  --       -- from subst-leaf-from-to, used in expanding below
  --       σ x = let (j₀ , m₀ , m₁) = x
  --                 q = –> (α j₀) m₀
  --             in j₀ , q , subst-leaf-from (ϕ j₀ q) (κ' j₀ q) k m₁

  --       L x = Leaf P (ψ k x) j
  --       w' = ψ k (subst-leaf-from (nd (f , ϕ)) κ k (subst-lf-to {w = nd (f , ϕ)} {κ = κ} (k₀ , p₀ , l₀)))

  --       glf = graft-leaf-from-to P w ψ₀ k (k₀ , lf₀ , lf₁)
  --       slf = subst-leaf-from-to (ϕ k₀ p₀') (κ' k₀ p₀') k l₀'
  --       tpl = transp!-pair-lem (λ x → Leaf P (ϕ k₀ x) k) (α k₀) p₀ l₀
        
  --       lem₀ = subst-lf-to {w = w'} (transport! L (ap σ glf ∙ (ap (λ x → k₀ , p₀' , x) slf ∙ ap (λ x → k₀ , x) tpl)) l₁)

  --                =⟨ transp!-∙ L (ap σ glf) (ap (λ x → k₀ , p₀' , x) slf ∙ ap (λ x → k₀ , x) tpl) l₁
  --                     |in-ctx (subst-lf-to {w = w'}) ⟩

  --              subst-lf-to {w = w'} (transport! L (ap σ glf) (transport! L (ap (λ x → k₀ , p₀' , x) slf ∙ ap (λ x → k₀ , x) tpl) l₁))

  --                =⟨ transp!-∙ L (ap (λ x → k₀ , p₀' , x) slf) (ap (λ x → k₀ , x) tpl) l₁
  --                     |in-ctx (λ x → subst-lf-to {w = w'} (transport! L (ap σ glf) x)) ⟩
                 
  --              subst-lf-to {w = w'} (transport! L (ap σ glf)
  --                                     (transport! L (ap (λ x → k₀ , p₀' , x) slf)
  --                                       (transport! L (ap (λ x → k₀ , x) tpl) l₁)))
                     
  --                =⟨ ! (transp!-ap L (λ x → k₀ , x) tpl l₁)
  --                    |in-ctx (λ x → subst-lf-to {w = w'} (transport! L (ap σ glf)
  --                            (transport! L (ap (λ x → k₀ , p₀' , x) slf) x))) ⟩ 

  --              subst-lf-to {w = w'} (transport! L (ap σ glf)
  --                                     (transport! L (ap (λ x → k₀ , p₀' , x) slf) l₁'))

  --                =⟨ ! (transp!-ap L (λ x → k₀ , p₀' , x) slf l₁')
  --                     |in-ctx (λ x → subst-lf-to {w = w'} (transport! L (ap σ glf) x)) ⟩ 

  --              subst-lf-to {w = w'} (transport! L (ap σ glf)
  --                                     (transport! (λ x → Leaf P (ψ k (k₀ , p₀' , x)) j) slf l₁'))

  --                =⟨ ! (transp!-ap L σ glf (transport! (λ x → Leaf P (ψ k (k₀ , p₀' , x)) j) slf l₁'))
  --                     |in-ctx (subst-lf-to {w = w'}) ⟩ 

  --              subst-lf-to {w = w'} (transport! (λ x → Leaf P (ψ k (σ x)) j) glf
  --                                     (transport! (λ x → Leaf P (ψ k (k₀ , p₀' , x)) j) slf l₁'))

  --                =⟨ transp!-→ (λ x → Leaf P (ψ k (σ x)) j) (λ x → Leaf P (ψ₁ k x) j) glf (λ t u → subst-lf-to {w = ψ k (σ t)} u) ⟩
                 
  --              transport! (λ x → Leaf P (ψ₁ k x) j) (graft-leaf-from-to P w ψ₀ k (k₀ , lf₀ , lf₁)) lf₂ ∎
        
  --       lem₁ = graft-leaf-to P (ϕ k₀ p₀') (ψ' k₀ p₀') j (k ,  l₀' , l₁')
    
  --                =⟨ transp!-Σ (λ x → Leaf P (ϕ k₀ x) k) (λ x y → Leaf P (ψ k (k₀ , x , y)) j) (<–-inv-r (α k₀) p₀) l₀ l₁
  --                     |in-ctx (λ x → graft-leaf-to P (ϕ k₀ p₀') (ψ' k₀ p₀') j (k , x)) ⟩

  --              graft-leaf-to P (ϕ k₀ p₀') (ψ' k₀ p₀') j (k , 
  --                (transport! (λ x → Σ (Leaf P (ϕ k₀ x) k) (λ l' → Leaf P (ψ k (k₀ , x , l')) j))
  --                            (<–-inv-r (α k₀) p₀) (l₀ , l₁)))

  --                =⟨ transp!-→ (λ x → Σ (Leaf P (ϕ k₀ x) k) (λ l' → Leaf P (ψ k (k₀ , x , l')) j))
  --                             (λ x → Leaf P (graft P (ϕ k₀ x) (ψ' k₀ x)) j) (<–-inv-r (α k₀) p₀)
  --                             (λ x y → graft-leaf-to P (ϕ k₀ x) (ψ' k₀ x) j (k , y))  ⟩ 

  --              transport! (λ x → Leaf P (graft P (ϕ k₀ x) (ψ' k₀ x)) j) (<–-inv-r (α k₀) p₀)
  --                         (graft-leaf-to P (ϕ k₀ p₀) (ψ' k₀ p₀) j (k , l₀ , l₁)) ∎

  --       ih' = let p₀' = –> (α k₀) (<– (α k₀) p₀)
  --             in subst-graft-lf-ovr (ϕ k₀ p₀') (ψ' k₀ p₀') (κ' k₀ p₀') (θ' k₀ p₀') j k l₀' l₁' 

  --   in ap (λ x → graft-lf-to P {w = subst (nd (f , ϕ)) κ} (k , graft-lf-to P (k₀ , lf₀ , lf₁) , x)) lem₀ ∙ᵈ
  --      graft-assoc-lf-ovr P w ψ₀ ψ₁ k₀ lf₀ k lf₁ j lf₂ ∙ᵈ
  --      ↓-ap-in (λ x → Leaf P x j) (graft P w)
  --              (↓-graft-Leaf-ih P H k₀ (<– (α k₀) p₀)
  --                (ih' ∙ᵈ ↓-ap-in (λ x → Leaf P x j) (subst (graft P (ϕ k₀ p₀') (ψ' k₀ p₀')))
  --                        (↓-subst-Leaf-ih (lem k₀ lf₀) lem₁)))


