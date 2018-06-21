{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Inspect

module PolyMonads where

  data Mnd : Type₀ → Type₁

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
  --  The pullback monad
  --
  
  module _ {I : Type₀} (M : Mnd I) (X : I → Type₀) where

    I-pb : Type₀
    I-pb = Σ I X

    γ-pb : I-pb → Type₀
    γ-pb (i , x) = Σ (γ M i) (λ c → (p : ρ M c) → X (τ M p))

    ρ-pb : {i : I-pb} → γ-pb i → Type₀
    ρ-pb {i , x} (c , δ) = ρ M c

    τ-pb : {i : I-pb} {c : γ-pb i} → ρ-pb {i = i} c → I-pb
    τ-pb {i , x} {c , δ} p = τ M p , δ p

    η-pb : (i : I-pb) → γ-pb i
    η-pb (i , x) = η M i , λ p → transport X (ap (τ M) (ηρ-η M i p)) x

    ηρ-contr-pb : (i : I-pb) → is-contr (ρ-pb {i = i} (η-pb i))
    ηρ-contr-pb (i , x) = ηρ-contr M i

    μ-pb : {i : I-pb} (c : γ-pb i) (ε : (p : ρ-pb {i = i} c) → γ-pb (τ-pb {i = i} {c = c} p)) → γ-pb i
    μ-pb {i , x} (c , δ) ε = μ M c (fst ∘ ε) , λ p → transport X (coh p) (ε' p)

      where coh : (p : ρ M (μ M c (fst ∘ ε))) → τ M (μρ-snd M (fst ∘ ε) p) == τ M p
            coh p = ap (τ M) (μρ-η M (fst ∘ ε) p)

            ε' : (p : ρ M (μ M c (fst ∘ ε))) → X (τ M (μρ-snd M (fst ∘ ε) p))
            ε' p = snd (ε (μρ-fst M (fst ∘ ε) p)) (μρ-snd M (fst ∘ ε) p)

    μρ-equiv-pb : {i : I-pb} {c : γ-pb i}
                  (ε : (p : ρ-pb {i = i} c) → γ-pb (τ-pb {i = i} {c = c} p)) → 
                  Σ (ρ-pb {i = i} c) (λ p₀ → ρ-pb {i = τ-pb {i = i} {c = c} p₀} (ε p₀)) ≃ ρ-pb {i = i} (μ-pb {i = i} c ε)
    μρ-equiv-pb {i , x} {c , δ} ε = μρ-equiv M (fst ∘ ε)
    
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
    graft-slc-ρ-to (dot i) δ₁ ε₁ (inr (p , q)) = transport! (ρ-slc ∘ ε₁) (ηρ-η M i p) q 
    graft-slc-ρ-to (box c δ ε) δ₁ ε₁ (inl (inl unit)) = inl unit
    graft-slc-ρ-to (box c δ ε) δ₁ ε₁ (inl (inr (p , q))) = inr (p , graft-slc-ρ-to (ε p) (δ₁' p) (ε₁' p) (inl q))
      where open BoxLocal δ ε δ₁ ε₁
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

    graft-slc-ρ-from-to : {i : I} {c : γ M i} (n : Nst c)
                          (δ : (p : ρ M c) → (γ M (τ M p)))
                          (ε : (p : ρ M c) → Nst (δ p))
                          (q : ρ-slc n ⊔ Σ (ρ M c) (ρ-slc ∘ ε)) → 
                          graft-slc-ρ-from n δ ε (graft-slc-ρ-to n δ ε q) == q
    graft-slc-ρ-from-to (dot i) δ ε (inl ())
    graft-slc-ρ-from-to (dot i) δ ε (inr (p , q)) =
      ap inr (pair= (ηρ-η M i p) (to-transp-↓ (ρ-slc ∘ ε) (ηρ-η M i p) q))
    graft-slc-ρ-from-to (box c δ ε) δ₁ ε₁ (inl (inl unit)) = idp
    graft-slc-ρ-from-to (box c δ ε) δ₁ ε₁ (inl (inr (p , q))) with
      graft-slc-ρ-from (ε p) (λ q → δ₁ (μρ M δ p q)) (λ q → ε₁ (μρ M δ p q)) 
        (graft-slc-ρ-to (ε p) (λ q → δ₁ (μρ M δ p q)) (λ q → ε₁ (μρ M δ p q)) (inl q)) |
        inspect (graft-slc-ρ-from (ε p) (λ q → δ₁ (μρ M δ p q)) (λ q → ε₁ (μρ M δ p q)) ∘
          graft-slc-ρ-to (ε p) (λ q → δ₁ (μρ M δ p q)) (λ q → ε₁ (μρ M δ p q))) (inl q)
    graft-slc-ρ-from-to (box c δ ε) δ₁ ε₁ (inl (inr (p , q))) | inl q₀ | ingraph e =
      ap (λ x → inl (inr (p , x))) (–> (inl=inl-equiv q₀ q) lem)
    
      where open BoxLocal δ ε δ₁ ε₁
      
            lem = inl q₀ =⟨ ! e ⟩
                  graft-slc-ρ-from (ε p) (δ₁' p) (ε₁' p) (graft-slc-ρ-to (ε p) (δ₁' p) (ε₁' p) (inl q))
                    =⟨ graft-slc-ρ-from-to (ε p) (δ₁' p) (ε₁' p) (inl q) ⟩
                  inl q ∎

    -- This branch is impossible!
    graft-slc-ρ-from-to (box c δ ε) δ₁ ε₁ (inl (inr (p , q))) | inr (p₀ , q₀) | ingraph e =
      ⊥-elim (inl≠inr q (p₀ , q₀) claim)

      where open BoxLocal δ ε δ₁ ε₁

            claim = inl q =⟨ ! (graft-slc-ρ-from-to (ε p) (δ₁' p) (ε₁' p) (inl q) ) ⟩
                    graft-slc-ρ-from (ε p) (δ₁' p) (ε₁' p) (graft-slc-ρ-to (ε p) (δ₁' p) (ε₁' p) (inl q)) =⟨ e ⟩ 
                    inr (p₀ , q₀) ∎

    graft-slc-ρ-from-to (box c δ ε) δ₁ ε₁ (inr (p , q)) with
      graft-slc-ρ-from (ε (μρ-fst M δ p))
        (λ q → δ₁ (μρ M δ (μρ-fst M δ p) q))
        (λ q → ε₁ (μρ M δ (μρ-fst M δ p) q))
        (graft-slc-ρ-to (ε (μρ-fst M δ p)) (λ q → δ₁ (μρ M δ (μρ-fst M δ p) q)) (λ q → ε₁ (μρ M δ (μρ-fst M δ p) q))
          (inr (μρ-snd M δ p , (transport! (ρ-slc ∘ snd) (pair= (μρ-η M δ p) (apd ε₁ (μρ-η M δ p))) q)))) |
          inspect ((graft-slc-ρ-from (ε (μρ-fst M δ p)) (λ q → δ₁ (μρ M δ (μρ-fst M δ p) q)) (λ q → ε₁ (μρ M δ (μρ-fst M δ p) q))) ∘
                   (graft-slc-ρ-to (ε (μρ-fst M δ p)) (λ q → δ₁ (μρ M δ (μρ-fst M δ p) q)) (λ q → ε₁ (μρ M δ (μρ-fst M δ p) q))))
                  (inr (μρ-snd M δ p , (transport! (ρ-slc ∘ snd) (pair= (μρ-η M δ p) (apd ε₁ (μρ-η M δ p))) q)))
    graft-slc-ρ-from-to (box c δ ε) δ₁ ε₁ (inr (p , q)) | inl q₀ | ingraph e =
      ⊥-elim (inr≠inl IH-arg q₀ claim)

      where open BoxLocal δ ε δ₁ ε₁

            p₀ = μρ-fst M δ p
            p₁ = μρ-snd M δ p

            coh = μρ-η M δ p
            
            IH-arg = (p₁ , transport! (ρ-slc ∘ snd) (pair= coh (apd ε₁ coh)) q)
            
            IH : graft-slc-ρ-from (ε (p₀)) (δ₁' (p₀)) (ε₁' (p₀))
                  (graft-slc-ρ-to (ε (p₀)) (δ₁' (p₀)) (ε₁' (p₀)) (inr IH-arg))
                  == inr IH-arg
            IH =   graft-slc-ρ-from-to (ε (p₀)) (δ₁' (p₀)) (ε₁' (p₀))
                   (inr (μρ-snd M δ p , (transport! (ρ-slc ∘ snd) (pair= (μρ-η M δ p) (apd ε₁ (μρ-η M δ p))) q))) 

            claim = inr IH-arg =⟨ ! IH ⟩
                    graft-slc-ρ-from (ε (p₀)) (δ₁' (p₀)) (ε₁' (p₀))
                      (graft-slc-ρ-to (ε (p₀)) (δ₁' (p₀)) (ε₁' (p₀)) (inr IH-arg)) =⟨ e ⟩ 
                    inl q₀ ∎
            
    graft-slc-ρ-from-to (box c δ ε) δ₁ ε₁ (inr (p , q)) | inr (p₀ , q₀) | ingraph e = ap inr lem

      where open BoxLocal δ ε δ₁ ε₁

            r₀ = μρ-fst M δ p
            r₁ = μρ-snd M δ p

            coh = μρ-η M δ p
            α = pair= coh (apd ε₁ coh)

            IH-arg = (r₁ , transport! (ρ-slc ∘ snd) (pair= coh (apd ε₁ coh)) q)
            
            IH : graft-slc-ρ-from (ε (r₀)) (δ₁' (r₀)) (ε₁' (r₀))
                  (graft-slc-ρ-to (ε (r₀)) (δ₁' (r₀)) (ε₁' (r₀)) (inr IH-arg))
                  == inr IH-arg
            IH =   graft-slc-ρ-from-to (ε (r₀)) (δ₁' (r₀)) (ε₁' (r₀))
                   (inr (μρ-snd M δ p , (transport! (ρ-slc ∘ snd) (pair= (μρ-η M δ p) (apd ε₁ (μρ-η M δ p))) q)))
                   
            lem₀ = inr (p₀ , q₀) =⟨ ! e ⟩
                   graft-slc-ρ-from (ε (r₀)) (δ₁' (r₀)) (ε₁' (r₀))
                     (graft-slc-ρ-to (ε (r₀)) (δ₁' (r₀)) (ε₁' (r₀)) (inr IH-arg)) =⟨ IH ⟩
                   inr IH-arg ∎
                   
            -- From this, we should learn that

            claim : p₀ == r₁
            claim = fst= (fst (inr=inr-equiv (p₀ , q₀) IH-arg) lem₀)

            snd-claim : q₀ == transport! (ρ-slc ∘ snd) α q [ ρ-slc ∘ ε₁ ∘ (μρ M δ r₀) ↓ claim ]
            snd-claim = snd= (fst (inr=inr-equiv (p₀ , q₀) IH-arg) lem₀)

            step₀ : transport! (ρ-slc ∘ snd) α q == q [ ρ-slc ∘ snd ↓ pair= coh (apd ε₁ coh) ]
            step₀ = to-transp-↓ (ρ-slc ∘ snd) α q

            step₁ : transport! (ρ-slc ∘ snd) α q == q [ ρ-slc ∘ ε₁ ↓ coh ]
            step₁ = ↓-apd-lem (λ _ n → ρ-slc n) step₀ 
      
            lem = μρ M δ r₀ p₀ , q₀
                     =⟨ pair= (ap (μρ M δ r₀) claim) (↓-ap-in (ρ-slc ∘ ε₁) (μρ M δ r₀) snd-claim) ⟩
                  μρ M δ r₀ r₁ , snd IH-arg
                     =⟨ pair= (μρ-η M δ p) step₁ ⟩ 
                  p , q ∎

    graft-slc-ρ-equiv : {i : I} {c : γ M i} (n : Nst c)
                        (δ : (p : ρ M c) → (γ M (τ M p)))
                        (ε : (p : ρ M c) → Nst (δ p)) → 
                        ρ-slc n ⊔ Σ (ρ M c) (ρ-slc ∘ ε) ≃ ρ-slc (graft-slc n δ ε)
    graft-slc-ρ-equiv n δ ε =
      equiv (graft-slc-ρ-to n δ ε) (graft-slc-ρ-from n δ ε)
            (graft-slc-ρ-to-from n δ ε) (graft-slc-ρ-from-to n δ ε)
    
    --
    --  Joining, and the equivalence of places
    --

    μ-slc : {i : I-slc} (c : γ-slc i) (δ : (p : ρ-slc c) → γ-slc (τ-slc p)) → γ-slc i
    μ-slc (dot i) κ = dot i
    μ-slc (box c δ ε) κ = graft-slc (κ (inl unit)) δ (λ p → μ-slc (ε p) (λ q → κ (inr (p , q))))

    μρ-slc-to : {i : I-slc} {c : γ-slc i}
                (κ : (p : ρ-slc c) → γ-slc (τ-slc p)) → 
                Σ (ρ-slc c) (ρ-slc ∘ κ) → ρ-slc (μ-slc c κ)
    μρ-slc-to {c = dot i} κ (() , _)
    μρ-slc-to {c = box c δ ε} κ (inl unit , q) =
      graft-slc-ρ-to (κ (inl unit)) δ (λ p → μ-slc (ε p) (λ q₀ → κ (inr (p , q₀)))) (inl q)
    μρ-slc-to {c = box c δ ε} κ (inr (p , q) , q₀) =
      graft-slc-ρ-to (κ (inl unit)) δ (λ p₁ → μ-slc (ε p₁) (λ q₁ → κ (inr (p₁ , q₁)))) (inr (p , μρ-slc-to (λ q₁ → κ (inr (p , q₁))) (q , q₀)))

    μρ-slc-from : {i : I-slc} {c : γ-slc i}
                  (κ : (p : ρ-slc c) → γ-slc (τ-slc p)) → 
                  ρ-slc (μ-slc c κ) → Σ (ρ-slc c) (ρ-slc ∘ κ) 
    μρ-slc-from {c = dot i} κ ()
    μρ-slc-from {c = box c δ ε} κ q with graft-slc-ρ-from (κ (inl unit)) δ (λ q₀ → μ-slc (ε q₀) (λ q₁ → κ (inr (q₀ , q₁)))) q
    μρ-slc-from {c = box c δ ε} κ q | inl q₀ = inl unit , q₀
    μρ-slc-from {c = box c δ ε} κ q | inr (p , q₀) = (inr (p , fst IH)) , snd IH

      where IH = μρ-slc-from {c = ε p} (λ q₁ → κ (inr (p , q₁))) q₀

    μρ-slc-to-from : {i : I-slc} {c : γ-slc i}
                     (κ : (p : ρ-slc c) → γ-slc (τ-slc p)) 
                     (q : ρ-slc (μ-slc c κ)) → 
                     μρ-slc-to κ (μρ-slc-from κ q) == q
    μρ-slc-to-from {c = dot i} κ ()
    μρ-slc-to-from {c = box c δ ε} κ q with
      graft-slc-ρ-from (κ (inl unit)) δ (λ q₀ → μ-slc (ε q₀) (λ q₁ → κ (inr (q₀ , q₁)))) q
        | inspect (graft-slc-ρ-from (κ (inl unit)) δ (λ q₀ → μ-slc (ε q₀) (λ q₁ → κ (inr (q₀ , q₁))))) q
    μρ-slc-to-from {c = box c δ ε} κ q | inl q₀ | ingraph e = lem

      where c' = (κ (inl unit))
            ε' = (λ p → μ-slc (ε p) (λ q₁ → κ (inr (p , q₁))))

            lem : graft-slc-ρ-to  c' δ  ε' (inl q₀) == q
            lem = graft-slc-ρ-to c' δ ε' (inl q₀) =⟨ ap (graft-slc-ρ-to c' δ ε') (! e) ⟩
                  graft-slc-ρ-to c' δ ε' (graft-slc-ρ-from c' δ ε' q) =⟨ graft-slc-ρ-to-from c' δ ε' q ⟩ 
                  q ∎

    μρ-slc-to-from {c = box c δ ε} κ q | inr (p , q₀) | ingraph e = lem

      where c' = (κ (inl unit))
            ε' = (λ p → μ-slc (ε p) (λ q₁ → κ (inr (p , q₁))))
            κ' = (λ q₁ → κ (inr (p , q₁)))

            lem = graft-slc-ρ-to c' δ ε' (inr (p , μρ-slc-to κ' (μρ-slc-from κ' q₀)))
                    =⟨ μρ-slc-to-from κ' q₀ |in-ctx (λ q₁ → graft-slc-ρ-to c' δ ε' (inr (p , q₁))) ⟩
                  graft-slc-ρ-to c' δ ε' (inr (p , q₀))
                    =⟨ ap (graft-slc-ρ-to c' δ ε') (! e) ⟩ 
                  graft-slc-ρ-to c' δ ε' (graft-slc-ρ-from c' δ ε' q)
                    =⟨ graft-slc-ρ-to-from c' δ ε' q ⟩ 
                  q ∎

    μρ-slc-from-to : {i : I-slc} {c : γ-slc i}
                     (κ : (p : ρ-slc c) → γ-slc (τ-slc p)) 
                     (q : Σ (ρ-slc c) (ρ-slc ∘ κ)) → 
                     μρ-slc-from κ (μρ-slc-to κ q) == q
    μρ-slc-from-to {c = dot i} κ (() , _)
    μρ-slc-from-to {c = box c δ ε} κ q with
      graft-slc-ρ-from (κ (inl unit)) δ (λ q₀ → μ-slc (ε q₀) (λ q₁ → κ (inr (q₀ , q₁)))) (μρ-slc-to κ q)
        | inspect (graft-slc-ρ-from (κ (inl unit)) δ (λ q₀ → μ-slc (ε q₀) (λ q₁ → κ (inr (q₀ , q₁))))) (μρ-slc-to κ q)
    μρ-slc-from-to {_} {box c δ ε} κ (inl unit , q) | inl q₁ | ingraph e =
      ap (λ z → inl unit , z) (–> (inl=inl-equiv q₁ q) lem )

      where c' = (κ (inl unit))
            ε' = (λ q₀ → μ-slc (ε q₀) (λ q₂ → κ (inr (q₀ , q₂))))

            lem = inl q₁ =⟨ ! e ⟩
                  graft-slc-ρ-from c' δ ε' (graft-slc-ρ-to c' δ ε' (inl q))
                    =⟨ graft-slc-ρ-from-to c' δ ε' (inl q) ⟩ 
                  inl q ∎

    μρ-slc-from-to {_} {box c δ ε} κ (inl unit , q) | inr q₁ | ingraph e =
      ⊥-elim (inr≠inl q₁ q lem)

      where c' = (κ (inl unit))
            ε' = (λ q₀ → μ-slc (ε q₀) (λ q₂ → κ (inr (q₀ , q₂))))

            lem = inr q₁ =⟨ ! e ⟩
                  graft-slc-ρ-from c' δ ε' (graft-slc-ρ-to c' δ ε' (inl q))
                    =⟨ graft-slc-ρ-from-to c' δ ε' (inl q) ⟩ 
                  inl q ∎

    μρ-slc-from-to {_} {box c δ ε} κ (inr (p , q) , q₀) | inl q₁ | ingraph e =
      ⊥-elim (inl≠inr q₁ pp lem)

      where c' = (κ (inl unit))
            ε' = (λ q₃ → μ-slc (ε q₃) (λ q₂ → κ (inr (q₃ , q₂))))
            pp = (p , μρ-slc-to (λ q₂ → κ (inr (p , q₂))) (q , q₀))

            lem = inl q₁ =⟨ ! e ⟩
                  graft-slc-ρ-from c' δ ε' (graft-slc-ρ-to c' δ ε' (inr pp))
                    =⟨ graft-slc-ρ-from-to c' δ ε' (inr pp) ⟩ 
                  inr pp ∎

    μρ-slc-from-to {_} {box c δ ε} κ (inr (p , q) , q₀) | inr (p₁ , q₁) | ingraph e =
      pair= (ap inr (pair= proj₀ (↓-Σ-fst ih-pth))) (↓-ap-in (ρ-slc ∘ κ) inr (↓-Σ-snd ih-pth))
      
      where c' = (κ (inl unit))
            ε' = (λ p₂ → μ-slc (ε p₂) (λ q₂ → κ (inr (p₂ , q₂))))
            q' = (inr (p , μρ-slc-to (λ q₂ → κ (inr (p , q₂))) (q , q₀))) 

            IH₀ : Σ (ρ-slc (ε p₁)) (ρ-slc ∘ (λ q₂ → κ (inr (p₁ , q₂))))
            IH₀ = μρ-slc-from {c = ε p₁} (λ q₂ → κ (inr (p₁ , q₂))) q₁

            IH : μρ-slc-from {c = ε p} (λ q₂ → κ (inr (p , q₂))) (μρ-slc-to (λ q₂ → κ (inr (p , q₂))) (q , q₀)) == (q , q₀)
            IH = μρ-slc-from-to (λ q₂ → κ (inr (p , q₂))) (q , q₀)
            
            have = inr (p₁ , q₁)
                     =⟨ ! e ⟩ 
                   graft-slc-ρ-from c' δ ε' (graft-slc-ρ-to c' δ ε' q')
                     =⟨ graft-slc-ρ-from-to c' δ ε' q' ⟩
                   inr (p , μρ-slc-to (λ q₂ → κ (inr (p , q₂))) (q , q₀)) ∎

            proj₀ : p₁ == p
            proj₀ = fst= (–> (inr=inr-equiv (p₁ , q₁) (p , μρ-slc-to (λ q₂ → κ (inr (p , q₂))) (q , q₀))) have)
            
            proj₁ : q₁ == μρ-slc-to (λ q₂ → κ (inr (p , q₂))) (q , q₀) [ ρ-slc ∘ ε' ↓ proj₀ ]
            proj₁ = snd= (–> (inr=inr-equiv (p₁ , q₁) (p , μρ-slc-to (λ q₂ → κ (inr (p , q₂))) (q , q₀))) have)

            ih-pth : IH₀ == q , q₀ [ (λ p₂ → Σ (ρ-slc (ε p₂)) (ρ-slc ∘ (λ q₂ → κ (inr (p₂ , q₂))))) ↓ proj₀ ]
            ih-pth = (apd↓-cst (λ {p₂} → μρ-slc-from {c = ε p₂} (λ q₂ → κ (inr (p₂ , q₂)))) proj₁) ∙'ᵈ IH

    μρ-equiv-slc : {i : I-slc} {c : γ-slc i}
                   (κ : (p : ρ-slc c) → γ-slc (τ-slc p)) → 
                   Σ (ρ-slc c) (ρ-slc ∘ κ) ≃ ρ-slc (μ-slc c κ)
    μρ-equiv-slc κ = equiv (μρ-slc-to κ) (μρ-slc-from κ)
      (μρ-slc-to-from κ) (μρ-slc-from-to κ)

  data Mnd where
    id : (I : Type₀) → Mnd I
    slc : {I : Type₀} (M : Mnd I) → Mnd (Σ I (γ M))
    pb : {I : Type₀} (M : Mnd I) (X : I → Type₀) → Mnd (Σ I X)

  --
  --  Decoding functions
  --
  
  γ (id I) i = ⊤
  γ (slc M) = γ-slc M
  γ (pb M X) = γ-pb M X

  ρ (id I) unit = ⊤
  ρ (slc M) = ρ-slc M
  ρ (pb M X) {i = i} = ρ-pb M X {i = i}

  τ (id I) {i} unit = i
  τ (slc M) = τ-slc M
  τ (pb M X) {i = i} {c = c} = τ-pb M X {i = i} {c = c}

  η (id I) _ = unit
  η (slc M) =  η-slc M
  η (pb M X) = η-pb M X

  μ (id I) unit _ = unit
  μ (slc M) = μ-slc M
  μ (pb M X) {i = i} = μ-pb M X {i = i}

  ηρ-contr (id I) _ = Unit-level
  ηρ-contr (slc M) = ηρ-contr-slc M
  ηρ-contr (pb M X) = ηρ-contr-pb M X

  μρ-equiv (id I) δ = equiv (λ { (unit , unit) → unit }) (λ { unit → unit , unit })
    (λ { unit → idp }) (λ { (unit , unit) → idp })
  μρ-equiv (slc M) = μρ-equiv-slc M 
  μρ-equiv (pb M X) {i = i} {c = c} = μρ-equiv-pb M X {i = i} {c = c}


