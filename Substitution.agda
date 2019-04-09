{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Grafting
open import PolyMagma

module Substitution {ℓ} {I : Type ℓ} (P : Poly I) where

  -- The polynomial underlying the substitution monad
  Subst : Poly (Σ I (Op P))
  Op Subst = InFrame P
  Param Subst (w , _) g = Node P w g

  SubstDecor : {i : I} (w : W P i) → Type ℓ
  SubstDecor w = (g : Ops P) → Node P w g → InFrame P g

  -- Elementary substitution.
  subst : {i : I} (w : W P i) (κ : SubstDecor w) → W P i
  subst (lf i) κ = lf i
  subst (nd (f , ϕ)) κ =
    let (w , α) = κ (_ , f) (inl idp)
        κ' j p g n = κ g (inr (j , p , n))
        ψ j l = subst (ϕ j (–> (α j) l)) (κ' j (–> (α j) l))
    in graft P w ψ

  module SubstLocal {i : I} (f : Op P i) (ϕ : Decor P f (W P))
    (κ : SubstDecor (nd (f , ϕ))) where

    ws : W P i
    ws = fst (κ (i , f) (inl idp))

    αs : Frame P ws f
    αs = snd (κ (i , f) (inl idp))

    κs : (j : I) (p : Param P f j) → SubstDecor (ϕ j p)
    κs j p g n = κ g (inr (j , p , n))

    ψs : Decor (Fr P) ws (W P)
    ψs j l = subst (ϕ j (–> (αs j) l)) (κs j (–> (αs j) l))

  -- Leaves in a substitution
  subst-leaf-to : {i : I} (w : W P i) (κ : SubstDecor w)
    → (j : I) → Leaf P w j → Leaf P (subst w κ) j 
  subst-leaf-to (lf i) κ j l = l
  subst-leaf-to (nd (f , ϕ)) κ j (k , p , l) = 
    let open SubstLocal f ϕ κ
        p' = –> (αs k) (<– (αs k) p)
        l' = transport! (λ x → Leaf P (ϕ k x) j) (<–-inv-r (αs k) p) l
    in graft-leaf-to P ws ψs j (k , <– (αs k) p , subst-leaf-to (ϕ k p') (κs k p') j l')

  subst-leaf-from : {i : I} (w : W P i) (κ : SubstDecor w)
    → (j : I) → Leaf P (subst w κ) j → Leaf P w j
  subst-leaf-from (lf i) κ j l = l
  subst-leaf-from (nd (f , ϕ)) κ j l = 
    let open SubstLocal f ϕ κ
        (k , l₀ , l₁) = graft-leaf-from P ws ψs j l
        p = –> (αs k) l₀ 
    in k , p , subst-leaf-from (ϕ k p) (κs k p) j l₁

  -- TODO: Making these un-abstract something like doubles the
  -- the typechecking time of Biased.  Why?

  abstract
  
    subst-leaf-to-from : {i : I} (w : W P i) (κ : SubstDecor w)
      → (j : I) (l : Leaf P (subst w κ) j)
      → subst-leaf-to w κ j (subst-leaf-from w κ j l) == l
    subst-leaf-to-from (lf i) κ j l = idp
    subst-leaf-to-from (nd (f , ϕ)) κ j l = 
      let (w , α) = κ (_ , f) (inl idp)
          κ' j p g n = κ g (inr (j , p , n))
          ψ j l = subst (ϕ j (–> (α j) l)) (κ' j (–> (α j) l))
          (k , l₀ , l₁) = graft-leaf-from P w ψ j l
          Qₛ x = Leaf P (subst (ϕ k x) (κ' k x)) j
          Qₗ x = Leaf P (ϕ k x) j
          p = –> (α k) l₀
          p' = (–> (α k) (<– (α k) p))
          l₁' = transport! Qₗ (<–-inv-r (α k) p) (subst-leaf-from (ϕ k p) _ j l₁)
          l₁'' = transport! Qₛ (<–-inv-r (α k) p) l₁
      in graft-leaf-to P w ψ j (k , <– (α k) p , subst-leaf-to (ϕ k p') _ j l₁')
           =⟨ ! (transp!-→ Qₛ Qₗ (<–-inv-r (α k) p) (λ x → subst-leaf-from (ϕ k x) _ j))
                |in-ctx (λ x → graft-leaf-to P w ψ j (k , <– (α k) p , subst-leaf-to (ϕ k p') _ j x)) ⟩ 
         graft-leaf-to P w ψ j (k , <– (α k) p ,
           subst-leaf-to (ϕ k p') _ j
             (subst-leaf-from (ϕ k (–> (α k) (<– (α k) p))) _ j l₁''))
           =⟨ subst-leaf-to-from (ϕ k p') _ j l₁''
                |in-ctx (λ x → graft-leaf-to P w ψ j (k , <– (α k) p , x)) ⟩ 
         graft-leaf-to P w ψ j (k , <– (α k) p , l₁'')
           =⟨ pair= (<–-inv-l (α k) l₀) (transp!-eqv-lem {C = Qₛ} (α k) l₀ l₁)
                |in-ctx (λ x → graft-leaf-to P w ψ j (k , x)) ⟩
         graft-leaf-to P w ψ j (k , l₀ , l₁)
           =⟨ graft-leaf-to-from P w ψ j l ⟩ 
         l ∎

  -- Is there some simpler way to do this?
  subst-leaf-from-to : {i : I} (w : W P i) (κ : SubstDecor w)
    → (j : I) (l : Leaf P w j)
    → subst-leaf-from w κ j (subst-leaf-to w κ j l) == l
  subst-leaf-from-to (lf i) κ .i idp = idp
  subst-leaf-from-to (nd (f , ϕ)) κ j (k , p , l) =
    let open SubstLocal f ϕ κ

        p' = –> (αs k) (<– (αs k) p)
        l' = transport! (λ x → Leaf P (ϕ k x) j) (<–-inv-r (αs k) p) l
        t = k , <– (αs k) p , subst-leaf-to (ϕ k p') (κs k p') j l'

        σ t = let (k , l₀ , l₁) = t
                  p₀ = –> (αs k) l₀
              in k , p₀  , subst-leaf-from (ϕ k p₀) (κs k p₀) j l₁

    in ap σ (graft-leaf-from-to P ws ψs j t) ∙
       ap (λ x → k , p' , x) (subst-leaf-from-to (ϕ k p') _ j l') ∙
       ap (λ x → k , x) (transp!-pair-lem (λ x → Leaf P (ϕ k x) j) (αs k) p l)
       
       -- ap σ (graft-leaf-from-to P ws ψs j t) ∙
       -- ap (λ x → k , x) (pair= (<–-inv-r (αs k) p) (subst-leaf-from-to (ϕ k p') (κs k p') j l' ∙ᵈ
       --                                              to-transp!!-↓ (λ x → Leaf P (ϕ k x) j) (<–-inv-r (αs k) p) l))

  subst-leaf-eqv : {i : I} (w : W P i) (κ : SubstDecor w)
    → (j : I) → Leaf P w j ≃ Leaf P (subst w κ) j 
  subst-leaf-eqv w κ j = equiv (subst-leaf-to w κ j) (subst-leaf-from w κ j)
    (subst-leaf-to-from w κ j) (subst-leaf-from-to w κ j)

  -- Nodes in a substitution
  subst-node-to : {i : I} (w : W P i) (κ : SubstDecor w) (g : Ops P)
    → Σ (Ops P) (λ h → Σ (Node P w h) (λ n → Node P (fst (κ h n)) g))
    → Node P (subst w κ) g
  subst-node-to (lf i) κ g (h , lift () , n₁)
  subst-node-to (nd (f , ϕ)) κ g (._ , inl idp , n₁) = 
    let open SubstLocal f ϕ κ
    in graft-node-to P ws ψs g (inl n₁)
  subst-node-to (nd (f , ϕ)) κ g (h , inr (k , p , n₀) , n₁) = 
    let open SubstLocal f ϕ κ
        l = <– (αs k) p
        p' = –> (αs k) l
        (n₀' , n₁') = transport! (λ x → Σ (Node P (ϕ k x) h) (λ n → Node P (fst (κs k x h n)) g))
                                 (<–-inv-r (αs k) p) (n₀ , n₁)
    in graft-node-to P ws ψs g (inr (k , <– (αs k) p , subst-node-to (ϕ k p') (κs k p') g (h , n₀' , n₁')))

        -- Hmmm.  Here you are backwards from your usual convention....
        -- i.e. you transport after as opposed to before ....
    --     n' = subst-node-to (ϕ k p) (κs k p) g (h , n₀ , n₁)
    --     Q x = Node P (subst (ϕ k x) (κs k x)) g
    -- in graft-node-to P ws ψs g (inr (k , <– (αs k) p , transport! Q (<–-inv-r (αs k) p) n'))

  subst-node-from : {i : I} (w : W P i) (κ : SubstDecor w) (g : Ops P)
    → Node P (subst w κ) g
    → Σ (Ops P) (λ h → Σ (Node P w h) (λ n → Node P (fst (κ h n)) g))
  subst-node-from (lf i) κ g (lift ())
  subst-node-from (nd (f , ϕ)) κ g n = ⊔-rec gleft gright (graft-node-from P ws ψs g n)
    where open SubstLocal f ϕ κ

          gleft : Node P ws g → Σ (Ops P) (λ h → Σ (Node P (nd (f , ϕ)) h) (λ n₁ → Node P (fst (κ h n₁)) g))
          gleft n₀ = (_ , f) , inl idp , n₀

          gright : Σ I (λ k → Σ (Leaf P ws k) (λ l → Node P (ψs k l) g))
            → Σ (Ops P) (λ h → Σ (Node P (nd (f , ϕ)) h) (λ n₁ → Node P (fst (κ h n₁)) g))
          gright (j , l , n) = let p = –> (αs j) l
                                   (h , n₀ , n₁) = subst-node-from (ϕ j p) (κs j p) g n
                               in h , inr (j , p , n₀) , n₁

  -- Okay, so like, this way, you have actual access to the recursor.
  -- But I guess you see now what the point of having a separate definition
  -- was like you do in the grafting module: then you can write and prove
  -- the second equation directly using the types ....
  subst-node-from-rec-left : {i : I} (f : Op P i)
    → (ϕ : Decor P f (W P)) (κ : SubstDecor (nd (f , ϕ)))
    → (g : Ops P) (n₀ : Node P (SubstLocal.ws f ϕ κ) g)
    → Σ (Ops P) (λ h → Σ (Node P (nd (f , ϕ)) h) (λ n → Node P (fst (κ h n)) g))
  subst-node-from-rec-left f ϕ κ g n₀ = (_ , f) , inl idp , n₀

  postulate
  
    subst-node-to-from : {i : I} (w : W P i) (κ : SubstDecor w)
      → (g : Ops P) (n : Node P (subst w κ) g)
      → subst-node-to w κ g (subst-node-from w κ g n) == n
    -- subst-node-to-from (lf i) κ g (lift ())
    -- subst-node-to-from (nd (f , ϕ)) κ g n =
    --   Coprod-elim {C = C} doneleft doneright (graft-node-from P ws ψs g n) ∙
    --   graft-node-to-from P ws ψs g n

    --   where open SubstLocal f ϕ κ

    --         gleft : Node P ws g → Σ (Ops P) (λ h → Σ (Node P (nd (f , ϕ)) h) (λ n₁ → Node P (fst (κ h n₁)) g))
    --         gleft n₀ = (_ , f) , inl idp , n₀

    --         gright : Σ I (λ k → Σ (Leaf P ws k) (λ l → Node P (ψs k l) g))
    --           → Σ (Ops P) (λ h → Σ (Node P (nd (f , ϕ)) h) (λ n₁ → Node P (fst (κ h n₁)) g))
    --         gright (j , l , n) = let p = –> (αs j) l
    --                                  (h , n₀ , n₁) = subst-node-from (ϕ j p) (κs j p) g n
    --                              in h , inr (j , p , n₀) , n₁

    --         C : Node P ws g ⊔ Σ I (λ k → Σ (Leaf P ws k) (λ l → Node P (ψs k l) g)) → Type ℓ
    --         C n = subst-node-to (nd (f , ϕ)) κ g (⊔-rec gleft gright n) == graft-node-to P ws ψs g n

    --         doneleft : (n₀ : Node P ws g) → C (inl n₀)
    --         doneleft n₀ = idp

    --         doneright : (b : Σ I (λ k → Σ (Leaf P ws k) (λ l → Node P (ψs k l) g))) → C (inr b)
    --         doneright (j , l , n) = ap (λ x → graft-node-to P ws ψs g (inr (j , x))) (pair= (<–-inv-l (αs j) l) {!!})
      
    subst-node-from-to : {i : I} (w : W P i)
      → (κ : (g : Ops P) → Node P w g → InFrame P g)
      → (g : Ops P) (n : Σ (Ops P) (λ h → Σ (Node P w h) (λ n → Node P (fst (κ h n)) g)))
      → subst-node-from w κ g (subst-node-to w κ g n) == n

  subst-node-eqv : {i : I} (w : W P i)
    → (κ : (g : Ops P) → Node P w g → InFrame P g) (g : Ops P)
    → Σ (Ops P) (λ h → Σ (Node P w h) (λ n → Node P (fst (κ h n)) g))
    ≃ Node P (subst w κ) g 
  subst-node-eqv w κ g = equiv (subst-node-to w κ g) (subst-node-from w κ g)
    (subst-node-to-from w κ g) (subst-node-from-to w κ g)


  --
  --  Abbreviations with implicit arguments
  --

  subst-lf-to : {i : I} {w : W P i}
    → {κ : (g : Ops P) → Node P w g → InFrame P g}
    → {j : I} → Leaf P w j → Leaf P (subst w κ) j 
  subst-lf-to {i} {w} {κ} {j} = subst-leaf-to w κ j

  subst-lf-from : {i : I} {w : W P i}
    → {κ : (g : Ops P) → Node P w g → InFrame P g}
    → {j : I} → Leaf P (subst w κ) j → Leaf P w j
  subst-lf-from {i} {w} {κ} {j} = subst-leaf-from w κ j

  subst-lf-to-from : {i : I} {w : W P i}
    → {κ : (g : Ops P) → Node P w g → InFrame P g}
    → {j : I} (l : Leaf P (subst w κ) j)
    → subst-leaf-to w κ j (subst-leaf-from w κ j l) == l
  subst-lf-to-from {i} {w} {κ} {j} =
    subst-leaf-to-from w κ j
    
  subst-lf-from-to : {i : I} {w : W P i}
    → {κ : (g : Ops P) → Node P w g → InFrame P g}
    → {j : I} (l : Leaf P w j)
    → subst-leaf-from w κ j (subst-leaf-to w κ j l) == l
  subst-lf-from-to {i} {w} {κ} {j} =
    subst-leaf-from-to w κ j

  subst-nd-to : {i : I} {w : W P i}
    → {κ : (g : Ops P) → Node P w g → InFrame P g}
    → {g : Ops P} → Σ (Ops P) (λ h → Σ (Node P w h) (λ n → Node P (fst (κ h n)) g))
    → Node P (subst w κ) g
  subst-nd-to {i} {w} {κ} {g} = subst-node-to w κ g
  
  subst-nd-from : {i : I} {w : W P i}
    → {κ : (g : Ops P) → Node P w g → InFrame P g}
    → {g : Ops P} → Node P (subst w κ) g
    → Σ (Ops P) (λ h → Σ (Node P w h) (λ n → Node P (fst (κ h n)) g))
  subst-nd-from {i} {w} {κ} {g} = subst-node-from w κ g

  --
  -- Path-over priciples
  --

  ↓-subst-Leaf-ih₀ : {i : I} {w : W P i}
    → {κ₀ κ₁ : (g : Ops P) → Node P w g → InFrame P g} (e : κ₀ == κ₁)
    → {j : I} {l₀ : Leaf P w j} {l₁ : Leaf P w j}
    → l₀ == l₁
    → subst-leaf-to w κ₀ j l₀
      == subst-leaf-to w κ₁ j l₁ [ (λ x → Leaf P (subst w x) j) ↓ e ]
  ↓-subst-Leaf-ih₀ idp idp = idp 

  ↓-subst-Leaf-ih : {i : I} {w : W P i}
    → {κ₀ κ₁ : (g : Ops P) → Node P w g → InFrame P g} 
    → (H : (g : Ops P) (n : Node P w g) → κ₀ g n == κ₁ g n)
    → {j : I} {l₀ : Leaf P w j} {l₁ : Leaf P w j}
    → l₀ == l₁
    → subst-leaf-to w κ₀ j l₀
      == subst-leaf-to w κ₁ j l₁ [ (λ x → Leaf P (subst w x) j) ↓ λ= (λ g → λ= (λ n → H g n)) ]
  ↓-subst-Leaf-ih H q = ↓-subst-Leaf-ih₀ (λ= (λ g → λ= (λ n → H g n))) q 

  ↓-subst-Node-ih₀ : {i : I} {w : W P i}
    → {κ₀ κ₁ : (g : Ops P) → Node P w g → InFrame P g} (e : κ₀ == κ₁)
    → {g h : Ops P} (n : Node P w g)
    → {n₀ : Node P (fst (κ₀ g n)) h} {n₁ : Node P (fst (κ₁ g n)) h}
    → n₀ == n₁ [ (λ x → Node P (fst x) h) ↓ app= (app= e g) n ]
    → subst-node-to w κ₀ h (g , n , n₀)
      == subst-node-to w κ₁ h (g , n , n₁) [ (λ x → Node P (subst w x) h) ↓ e ]
  ↓-subst-Node-ih₀ idp n idp = idp

  ↓-subst-Node-ih : {i : I} {w : W P i}
    → {κ₀ κ₁ : (g : Ops P) → Node P w g → InFrame P g}
    → (H : (g : Ops P) (n : Node P w g) → κ₀ g n == κ₁ g n)
    → {g h : Ops P} (n : Node P w g)
    → {n₀ : Node P (fst (κ₀ g n)) h} {n₁ : Node P (fst (κ₁ g n)) h}
    → n₀ == n₁ [ (λ x → Node P (fst x) h) ↓ H g n ]
    → subst-node-to w κ₀ h (g , n , n₀)
      == subst-node-to w κ₁ h (g , n , n₁)
           [ (λ x → Node P (subst w x) h) ↓ λ= (λ g → λ= (λ n → H g n)) ]
  ↓-subst-Node-ih H {g} {h} n {n₀} {n₁} q = ↓-subst-Node-ih₀ (λ= (λ g → λ= (λ n → H g n))) n
    (transport (λ y → n₀ == n₁ [ (λ x → Node P (fst x) h) ↓ y ])
               (! (app=-β (H g) n) ∙ ap (λ x → app= x n) (! (app=-β (λ k → λ= (H k)) g))) q) 

  -- The Substitution Magma

  open BiasedMgm
  
  subst-η : (f : Ops P) → InFrame P f
  subst-η (_ , f) = corolla P f , corolla-frm P f

  -- subst-η-dec : {i : I} (w : W P i) →
  --   (g : Ops P) (n : Node P w g) → InFrame P g
  -- subst-η-dec w g n = subst-η g

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

  subst-frm-∘ : {i : I} {f : Op P i} {w : W P i}
    → (α : Frame P w f)
    → (κ : (g : Ops P) → Node P w g → InFrame P g)
    → Frame P (subst w κ) f
  subst-frm-∘ α κ j = α j ∘e (subst-leaf-eqv _ κ j)⁻¹

  subst-γ : (f : Ops P) (wα : InFrame P f)
    → (κ : (g : Ops P) → Node P (fst wα) g → InFrame P g) 
    → InFrame P f
  subst-γ (i , f) (w , α) κ =
    subst w κ , subst-frm-∘ α κ

  SubstBiasedMgm : BiasedMgm Subst
  η SubstBiasedMgm = subst-η
  η-frm SubstBiasedMgm = subst-η-frm
  γ SubstBiasedMgm (w , α) κ = subst w κ , subst-frm-∘ α κ
  γ-frm SubstBiasedMgm (w , α) κ = subst-node-eqv w κ

  SubstMgm : PolyMagma Subst
  SubstMgm = BsdMgm SubstBiasedMgm
  
  -- These replace flatten and bd-frame with the multiplication
  -- derived from the general framework....
  
  μ-subst : {f : Ops P} → W Subst f → Op Subst f
  μ-subst = μ-bsd SubstBiasedMgm

  μ-frm-subst : {f : Ops P} (pd : W Subst f) → Frame Subst pd (μ-subst pd)
  μ-frm-subst pd = μ-bsd-frm SubstBiasedMgm pd
