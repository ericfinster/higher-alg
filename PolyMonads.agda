{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Inspect

module PolyMonads where

  data Mnd : Type₀ → Type₁

  postulate
  
    γ : {I : Type₀} (M : Mnd I) → I → Type₀
    ρ : {I : Type₀} (M : Mnd I) {i : I} → γ M i → Type₀
    τ : {I : Type₀} (M : Mnd I) {i : I} {c : γ M i} → ρ M c → I

    η : {I : Type₀} (M : Mnd I) → (i : I) → γ M i
    μ : {I : Type₀} (M : Mnd I) {i : I} (c : γ M i) (δ : (p : ρ M c) → γ M (τ M p)) → γ M i

    ηρ-contr : {I : Type₀} (M : Mnd I) (i : I) → is-contr (ρ M (η M i))
    μρ-equiv : {I : Type₀} (M : Mnd I) {i : I} {c : γ M i}
               (δ : (p : ρ M c) → γ M (τ M p)) →
               Σ (ρ M c) (ρ M ∘ δ) ≃ ρ M (μ M c δ)

  --
  --  Place helper functions
  --
  
  ηρ : {I : Type₀} (M : Mnd I) (i : I) → ρ M (η M i)
  ηρ M i = fst (has-level-apply (ηρ-contr M i))
  
  ηρ-η : {I : Type₀} (M : Mnd I) (i : I) (p : ρ M (η M i)) → ηρ M i == p
  ηρ-η M i p = snd (has-level-apply (ηρ-contr M i)) p

  μρ : {I : Type₀} (M : Mnd I) {i : I} {c : γ M i}
       (δ : (p : ρ M c) → γ M (τ M p)) 
       (p₀ : ρ M c) (p₁ : ρ M (δ p₀)) → ρ M (μ M c δ)
  μρ M δ p₀ p₁ = fst (μρ-equiv M δ) (p₀ , p₁)

  μρ-fst : {I : Type₀} (M : Mnd I) {i : I} {c : γ M i}
           (δ : (p : ρ M c) → γ M (τ M p)) → ρ M (μ M c δ) → ρ M c
  μρ-fst M δ p = fst (is-equiv.g (snd (μρ-equiv M δ)) p)

  μρ-snd : {I : Type₀} (M : Mnd I) {i : I} {c : γ M i}
           (δ : (p : ρ M c) → γ M (τ M p)) 
           (pp : ρ M (μ M c δ)) → ρ M (δ (μρ-fst M δ pp))
  μρ-snd M δ p = snd (is-equiv.g (snd (μρ-equiv M δ)) p)
  
  μρ-η : {I : Type₀} (M : Mnd I) {i : I} {c : γ M i}
         (δ : (p : ρ M c) → γ M (τ M p))
         (p : ρ M (μ M c δ)) → μρ M δ (μρ-fst M δ p) (μρ-snd M δ p) == p
  μρ-η M δ p = is-equiv.f-g (snd (μρ-equiv M δ)) p

  μρ-β : {I : Type₀} (M : Mnd I) {i : I} {c : γ M i}
             (δ : (p : ρ M c) → γ M (τ M p))
             (p₀ : ρ M c) (p₁ : ρ M (δ p₀)) → 
             is-equiv.g (snd (μρ-equiv M δ)) (μρ M δ p₀ p₁) == (p₀ , p₁)
  μρ-β M δ p₀ p₁ = is-equiv.g-f (snd (μρ-equiv M δ)) (p₀ , p₁)

  μρ-fst-β : {I : Type₀} (M : Mnd I) {i : I} {c : γ M i}
             (δ : (p : ρ M c) → γ M (τ M p))
             (p₀ : ρ M c) (p₁ : ρ M (δ p₀)) → 
             μρ-fst M δ (μρ M δ p₀ p₁) == p₀
  μρ-fst-β M δ p₀ p₁ = fst= (is-equiv.g-f (snd (μρ-equiv M δ)) (p₀ , p₁))
  
  μρ-snd-β : {I : Type₀} (M : Mnd I) {i : I} {c : γ M i}
             (δ : (p : ρ M c) → γ M (τ M p))
             (p₀ : ρ M c) (p₁ : ρ M (δ p₀)) → 
             μρ-snd M δ (μρ M δ p₀ p₁) == p₁ [ (λ p → ρ M (δ p)) ↓ μρ-fst-β M δ p₀ p₁ ] 
  μρ-snd-β M δ p₀ p₁ = snd= (is-equiv.g-f (snd (μρ-equiv M δ)) (p₀ , p₁))

  μρ-adj-l : {I : Type₀} (M : Mnd I) {i : I} {c : γ M i}
             (δ : (p : ρ M c) → γ M (τ M p))
             (p₀ : ρ M c) (p₁ : ρ M (δ p₀)) → ap (fst (μρ-equiv M δ))
      (is-equiv.g-f (snd (μρ-equiv M δ)) (p₀ , p₁)) == μρ-η M δ (μρ M δ p₀ p₁)
  μρ-adj-l M δ p₀ p₁ = is-equiv.adj (snd (μρ-equiv M δ)) (p₀ , p₁)
  
  postulate
  
    ηp-compat : {I : Type₀} {M : Mnd I} (i : I) →
                τ M (ηρ M i) ↦ i

    {-# REWRITE ηp-compat #-}

    μρ-compat : {I : Type₀} {M : Mnd I} (i : I) (c : γ M i)
                (δ : (p : ρ M c) → γ M (τ M p))
                (p : ρ M c) (q : ρ M (δ p)) → ρ M (μ M c δ) →
                τ M (μρ M δ p q) ↦ τ M q

    {-# REWRITE μρ-compat #-}

    unit-l : {I : Type₀} {M : Mnd I} (i : I) (c : γ M i) →
             μ M c (λ p → η M (τ M p)) ↦ c

    {-# REWRITE unit-l #-}

    unit-r : {I : Type₀} {M : Mnd I} (i : I) (δ : (p : ρ M (η M i)) → γ M (τ M p)) →
             μ M (η M i) δ ↦ δ (ηρ M i)

    {-# REWRITE unit-r #-}
    
    assoc : {I : Type₀} {M : Mnd I} {i : I} {c : γ M i}
            (δ : (p : ρ M c) → γ M (τ M p))
            (ε : (q : ρ M (μ M c δ)) → γ M (τ M q)) →
            μ M (μ M c δ) ε ↦ μ M c (λ p → μ M (δ p) (λ q → ε (μρ M δ p q))) 

    {-# REWRITE assoc #-}

  --
  -- The slice monad
  --
  
  module _ {I : Type₀} (M : Mnd I) where

    I-slc : Type₀
    I-slc = Σ I (γ M)

    data Nst : {i : I} → (c : γ M i) → Type₀ where
      dot : (i : I) → Nst (η M i)
      box : {i : I} (c : γ M i)
            (δ : (p : ρ M c) → γ M (τ M p))
            (ε : (p : ρ M c) → Nst (δ p)) →
            Nst (μ M c δ)

    γ-slc : I-slc → Type₀
    γ-slc (i , c) = Nst c
    
    ρ-slc : {i : I} {c : γ M i} (n : Nst c) → Type₀
    ρ-slc (dot i) = ⊥
    ρ-slc (box c δ ε) = ⊤ ⊔ Σ (ρ M c) (λ p → ρ-slc (ε p))

    τ-slc : {i : I} {c : γ M i} {n : Nst c} (p : ρ-slc n) → I-slc
    τ-slc {n = dot i} ()
    τ-slc {n = box c δ ε} (inl unit) = _ , c
    τ-slc {n = box c δ ε} (inr (p , q)) = τ-slc {n = ε p} q

    η-slc : (i : I-slc) → γ-slc i
    η-slc (i , c) = (box c (λ p → η M (τ M p)) (λ p → dot (τ M p)))

    ηρ-slc : (i : I-slc) → ρ-slc (η-slc i)
    ηρ-slc (i , c) = inl unit
    
    ηρ-η-slc : (i : I-slc) (p : ρ-slc (η-slc i)) → ηρ-slc i == p
    ηρ-η-slc (i , c) (inl unit) = idp
    ηρ-η-slc (i , c) (inr (_ , ()))

    ηρ-contr-slc : (i : I-slc) → is-contr (ρ-slc (η-slc i))
    ηρ-contr-slc i = has-level-in (ηρ-slc i , ηρ-η-slc i)

    module BoxLocal {i : I} {c : γ M i}
                 (δ : (p : ρ M c) → γ M (τ M p))
                 (ε : (p : ρ M c) → Nst (δ p))
                 (δ₁ : (p : ρ M (μ M c δ)) → γ M (τ M p))
                 (ε₁ : (p : ρ M (μ M c δ)) → Nst (δ₁ p)) where

      δ₁' : (p : ρ M c) → (q : ρ M (δ p)) → γ M (τ M q)
      δ₁' p q = δ₁ (μρ M δ p q)

      ε₁' : (p : ρ M c) → (q : ρ M (δ p)) → Nst (δ₁' p q)
      ε₁' p q = ε₁ (μρ M δ p q)
      
      δ' : (p : ρ M c) → γ M (τ M p)
      δ' p = μ M (δ p) (δ₁' p)

    --
    --  Grafting, and the equivalence of places
    --
    
    graft-slc : {i : I} {c : γ M i} (n : Nst c)
                (δ : (p : ρ M c) → γ M (τ M p))
                (ε : (p : ρ M c) → Nst (δ p)) →
                Nst (μ M c δ)
    graft-slc (dot i) δ ε = ε (ηρ M i)
    graft-slc (box c δ ε) δ₁ ε₁ = let open BoxLocal δ ε δ₁ ε₁ in
      box c δ' (λ p → graft-slc (ε p) (δ₁' p) (ε₁' p))

    graft-slc-ρ-to : {i : I} {c : γ M i} (n : Nst c)
                     (δ : (p : ρ M c) → γ M (τ M p))
                     (ε : (p : ρ M c) → Nst (δ p)) → 
                     ρ-slc n ⊔ Σ (ρ M c) (ρ-slc ∘ ε) → ρ-slc (graft-slc n δ ε)
    graft-slc-ρ-to (dot i) δ ε (inl ())
    graft-slc-ρ-to (box c δ ε) δ₁ ε₁ (inl (inl unit)) = inl unit
    graft-slc-ρ-to (box c δ ε) δ₁ ε₁ (inl (inr (p , q))) = inr (p , graft-slc-ρ-to (ε p) (δ₁' p) (ε₁' p) (inl q))
      where open BoxLocal δ ε δ₁ ε₁
    graft-slc-ρ-to (dot i) δ₁ ε₁ (inr (p , q)) = transport! (ρ-slc ∘ ε₁) (ηρ-η M i p) q 
    graft-slc-ρ-to (box c δ ε) δ₁ ε₁ (inr (p , q)) = inr (p₀ , IH)
      where open BoxLocal δ ε δ₁ ε₁

            p₀ = μρ-fst M δ p
            p₁ = μρ-snd M δ p

            coh : μρ M δ p₀ p₁ == p
            coh = μρ-η M δ p 

            P : Σ (ρ M (μ M c δ)) (Nst ∘ δ₁) → Type₀
            P (r , n) = ρ-slc n

            IH : ρ-slc (graft-slc (ε p₀) (δ₁' p₀) (ε₁' p₀))
            IH = graft-slc-ρ-to (ε p₀) (δ₁' p₀) (ε₁' p₀) (inr (p₁ , (transport! P (pair= coh (apd ε₁ coh)) q)))

    graft-slc-ρ-from : {i : I} {c : γ M i} (n : Nst c)
                  (δ : (p : ρ M c) → (γ M (τ M p)))
                  (ε : (p : ρ M c) → Nst (δ p)) →
                  ρ-slc (graft-slc n δ ε) → ρ-slc n ⊔ Σ (ρ M c) (ρ-slc ∘ ε) 
    graft-slc-ρ-from (dot i) δ₁ ε₁ q = inr (ηρ M i , q)
    graft-slc-ρ-from (box c δ ε) δ₁ ε₁ (inl unit) = inl (inl unit)
    graft-slc-ρ-from (box c δ ε) δ₁ ε₁ (inr (p , q)) with let open BoxLocal δ ε δ₁ ε₁ in graft-slc-ρ-from (ε p) (δ₁' p) (ε₁' p) q 
    graft-slc-ρ-from (box c δ ε) δ₁ ε₁ (inr (p , q)) | inl q₀ = inl (inr (p , q₀))
    graft-slc-ρ-from (box c δ ε) δ₁ ε₁ (inr (p , q)) | inr (p₀ , q₀) = inr (μρ M δ p p₀ , q₀)

    graft-slc-ρ-to-from : {i : I} {c : γ M i} (n : Nst c)
                          (δ : (p : ρ M c) → (γ M (τ M p)))
                          (ε : (p : ρ M c) → Nst (δ p))
                          (q : ρ-slc (graft-slc n δ ε)) →
                          graft-slc-ρ-to n δ ε (graft-slc-ρ-from n δ ε q) == q
    graft-slc-ρ-to-from (dot i) δ₁ ε₁ q = ap (λ e → transport! (ρ-slc ∘ ε₁) e q) coh

      where coh : ηρ-η M i (ηρ M i) == idp
            coh = contr-has-all-paths {{ (has-level-apply (raise-level ⟨-2⟩ (ηρ-contr M i)) (ηρ M i) (ηρ M i)) }}
                    (ηρ-η M i (ηρ M i)) idp
                    
    graft-slc-ρ-to-from (box c δ ε) δ₁ ε₁ (inl unit) = idp
    graft-slc-ρ-to-from (box c δ ε) δ₁ ε₁ (inr (p , q)) with
      graft-slc-ρ-from (ε p) (λ q → δ₁ (μρ M δ p q)) (λ q → ε₁ (μρ M δ p q)) q |
        inspect (graft-slc-ρ-from (ε p) (λ q → δ₁ (μρ M δ p q)) (λ q → ε₁ (μρ M δ p q))) q
        
    graft-slc-ρ-to-from (box c δ ε) δ₁ ε₁ (inr (p , q)) | inl q₀ | ingraph e = ap (λ q₁ → inr (p , q₁)) lem

      where open BoxLocal δ ε δ₁ ε₁

            lem = graft-slc-ρ-to (ε p) (δ₁' p) (ε₁' p) (inl q₀)
                    =⟨ ! e |in-ctx (λ q₁ → graft-slc-ρ-to (ε p) (δ₁' p) (ε₁' p) q₁) ⟩
                  graft-slc-ρ-to (ε p) (δ₁' p) (ε₁' p) (graft-slc-ρ-from (ε p) (δ₁' p) (ε₁' p) q)
                    =⟨ graft-slc-ρ-to-from (ε p) (δ₁' p) (ε₁' p) q ⟩ 
                  q ∎
                  
    graft-slc-ρ-to-from (box c δ ε) δ₁ ε₁ (inr (p , q)) | inr (p₀ , q₀) | ingraph e = ap inr lem

      where open BoxLocal δ ε δ₁ ε₁

            r₀ = μρ-fst M δ (μρ M δ p p₀)
            r₁ = μρ-snd M δ (μρ M δ p p₀)

            coh = μρ-η M δ (μρ M δ p p₀)

            α = pair= coh (apd ε₁ coh)
            β = pair= (μρ-fst-β M δ p p₀) (μρ-snd-β M δ p p₀)
            
            coh-adj : ap (fst (μρ-equiv M δ)) β == coh
            coh-adj =  transport (λ x → ap (fst (μρ-equiv M δ)) x == coh)
                         (pair=-η (is-equiv.g-f (snd (μρ-equiv M δ)) (p , p₀))) 
                         (μρ-adj-l M δ p p₀)
            
            step₀ : transport! (ρ-slc ∘ snd) α q₀ == q₀ [ ρ-slc ∘ snd ↓ pair= coh (apd ε₁ coh) ]
            step₀ = to-transp-↓ (ρ-slc ∘ snd) α q₀

            step₁ : transport! (ρ-slc ∘ snd) α q₀ == q₀ [ ρ-slc ∘ ε₁ ↓ coh ]
            step₁ = ↓-apd-lem (λ _ n → ρ-slc n) step₀ 

            step₂ : transport! (ρ-slc ∘ snd) α q₀ == q₀ [ ρ-slc ∘ ε₁ ↓ ap (fst (μρ-equiv M δ)) β ]
            step₂ = transport! (λ x → transport! (ρ-slc ∘ snd) α q₀ == q₀ [ ρ-slc ∘ ε₁ ↓ x ]) coh-adj step₁

            step₃ : transport! (ρ-slc ∘ snd) α q₀ == q₀ [ ρ-slc ∘ ε₁ ∘ (fst (μρ-equiv M δ)) ↓ β ]
            step₃ = ↓-ap-out (ρ-slc ∘ ε₁) (fst (μρ-equiv M δ)) β step₂

            lem = (r₀ , graft-slc-ρ-to (ε r₀) (δ₁' r₀) (ε₁' r₀) (inr (r₁ , (transport! (ρ-slc ∘ snd) α q₀))))
                    =⟨ pair= (μρ-fst-β M δ p p₀) (apd↓-cst (λ {s} x → graft-slc-ρ-to (ε s) (δ₁' s) (ε₁' s) (inr x)) (↓-Σ-in (μρ-snd-β M δ p p₀) step₃)) ⟩
                  (p , graft-slc-ρ-to (ε p) (δ₁' p) (ε₁' p) (inr (p₀ , q₀)))
                    =⟨ ! e |in-ctx (λ q₀ → (p , graft-slc-ρ-to (ε p) (δ₁' p) (ε₁' p) q₀)) ⟩ 
                  (p , graft-slc-ρ-to (ε p) (δ₁' p) (ε₁' p) (graft-slc-ρ-from (ε p) (δ₁' p) (ε₁' p) q))
                    =⟨ graft-slc-ρ-to-from (ε p) (δ₁' p) (ε₁' p) q |in-ctx (λ q₁ → (p , q₁)) ⟩ 
                  (p , q) ∎

    --
    --  Joining, and the equivalence of places
    --

  --   μ-slc : {i : I-slc} (c : γ-slc i) (δ : (p : ρ-slc c) → γ-slc (τ-slc p)) → γ-slc i
  --   μ-slc (dot i) κ = dot i
  --   μ-slc (box c δ ε) κ = graft-slc (κ (inl unit)) δ (λ p → μ-slc (ε p) (λ q → κ (inr (p , q))))

  --   μρ-slc : {i : I-slc} {c : γ-slc i}
  --            (κ : (p : ρ-slc c) → γ-slc (τ-slc p)) 
  --            (p₀ : ρ-slc c) (p₁ : ρ-slc (κ p₀)) → 
  --            ρ-slc (μ-slc c κ)
  --   μρ-slc {c = dot i} κ () _
  --   μρ-slc {c = box c δ ε} κ (inl unit) q =
  --     graft-slc-ρ-to (κ (inl unit)) δ (λ p → μ-slc (ε p) (λ q₀ → κ (inr (p , q₀)))) (inl q)
  --   μρ-slc {c = box c δ ε} κ (inr (p , q₀)) q =
  --     graft-slc-ρ-to (κ (inl unit)) δ (λ p₁ → μ-slc (ε p₁) (λ q₁ → κ (inr (p₁ , q₁)))) (inr (p , μρ-slc (λ q₁ → κ (inr (p , q₁))) q₀ q))

  --   μρ-fst-slc : {i : I-slc} {c : γ-slc i}
  --                (κ : (q : ρ-slc c) → γ-slc (τ-slc q))
  --                (q : ρ-slc (μ-slc c κ)) → ρ-slc c
  --   μρ-fst-slc {c = dot i} κ ()
  --   μρ-fst-slc {c = box c δ ε} κ q with graft-slc-ρ-from (κ (inl unit)) δ (λ q₀ → μ-slc (ε q₀) (λ q₁ → κ (inr (q₀ , q₁)))) q
  --   μρ-fst-slc {c = box c δ ε} κ q | inl q₀ = inl unit
  --   μρ-fst-slc {c = box c δ ε} κ q | inr (p , q₀) = inr (p , μρ-fst-slc {c = ε p} (λ q₁ → κ (inr (p , q₁))) q₀)
             
  --   μρ-snd-slc : {i : I-slc} {c : γ-slc i}
  --                (κ : (q : ρ-slc c) → γ-slc (τ-slc q))
  --                (q : ρ-slc (μ-slc c κ)) → ρ-slc (κ (μρ-fst-slc κ q))
  --   μρ-snd-slc {c = dot i} κ ()
  --   μρ-snd-slc {c = box c δ ε} κ q with graft-slc-ρ-from (κ (inl unit)) δ (λ q₀ → μ-slc (ε q₀) (λ q₁ → κ (inr (q₀ , q₁)))) q
  --   μρ-snd-slc {c = box c δ ε} κ q | inl q₀ = q₀
  --   μρ-snd-slc {c = box c δ ε} κ q | inr (p , q₀) = μρ-snd-slc {c = ε p} (λ q₁ → κ (inr (p , q₁))) q₀

  --   μρ-η-slc : {i : I-slc} {c : γ-slc i}
  --              (κ : (q : ρ-slc c) → γ-slc (τ-slc q))
  --              (q : ρ-slc (μ-slc c κ)) →
  --              μρ-slc κ (μρ-fst-slc κ q) (μρ-snd-slc κ q) == q
  --   μρ-η-slc {c = dot i} κ ()
  --   μρ-η-slc {c = box c δ ε} κ q with graft-slc-ρ-from (κ (inl unit)) δ (λ q₀ → μ-slc (ε q₀) (λ q₁ → κ (inr (q₀ , q₁)))) q
  --                                     | inspect (graft-slc-ρ-from (κ (inl unit)) δ (λ q₀ → μ-slc (ε q₀) (λ q₁ → κ (inr (q₀ , q₁))))) q
  --   μρ-η-slc {c = box c δ ε} κ q | inl q₀ | ingraph e = lem
    
  --     where c' = (κ (inl unit))
  --           ε' = (λ p → μ-slc (ε p) (λ q₁ → κ (inr (p , q₁))))

  --           lem : graft-slc-ρ-to  c' δ  ε' (inl q₀) == q
  --           lem = graft-slc-ρ-to c' δ ε' (inl q₀) =⟨ ap (graft-slc-ρ-to c' δ ε') (! e) ⟩
  --                 graft-slc-ρ-to c' δ ε' (graft-slc-ρ-from c' δ ε' q) =⟨ graft-slc-ρ-to-from c' δ ε' q ⟩ 
  --                 q ∎
    
  --   μρ-η-slc {c = box c δ ε} κ q | inr (p , q₀) | ingraph e = lem

  --     where c' = (κ (inl unit))
  --           ε' = (λ p → μ-slc (ε p) (λ q₁ → κ (inr (p , q₁))))
  --           κ' = (λ q₁ → κ (inr (p , q₁)))
            
  --           IH : μρ-slc κ' (μρ-fst-slc κ' q₀) (μρ-snd-slc κ' q₀) == q₀
  --           IH = μρ-η-slc κ' q₀

  --           lem = graft-slc-ρ-to c' δ ε' (inr (p , μρ-slc κ' (μρ-fst-slc κ' q₀) (μρ-snd-slc κ' q₀)))
  --                   =⟨ IH |in-ctx (λ q₁ → graft-slc-ρ-to c' δ ε' (inr (p , q₁))) ⟩
  --                 graft-slc-ρ-to c' δ ε' (inr (p , q₀))
  --                   =⟨ ap (graft-slc-ρ-to c' δ ε') (! e) ⟩ 
  --                 graft-slc-ρ-to c' δ ε' (graft-slc-ρ-from c' δ ε' q)
  --                   =⟨ graft-slc-ρ-to-from c' δ ε' q ⟩ 
  --                 q ∎

  data Mnd where
    id : (I : Type₀) → Mnd I
    slc : {I : Type₀} (M : Mnd I) → Mnd (Σ I (γ M))
    pb : {I : Type₀} (M : Mnd I) (X : I → Type₀) → Mnd (Σ I X)

