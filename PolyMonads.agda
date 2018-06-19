{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Inspect

module PolyMonads where

  data Mnd : Type₀ → Type₁

  γ : {I : Type₀} (M : Mnd I) → I → Type₀
  ρ : {I : Type₀} (M : Mnd I) {i : I} → γ M i → Type₀
  τ : {I : Type₀} (M : Mnd I) {i : I} {c : γ M i} → ρ M c → I

  ⟦_⟧ : {I : Type₀} (M : Mnd I) → (I → Set) → I → Set
  ⟦ M ⟧ X i = Σ (γ M i) (λ c → (p : ρ M c) → X (τ M p))

  postulate
  
    ρ-dec : {I : Type₀} (M : Mnd I) {i : I} (c : γ M i) → has-dec-eq (ρ M c)

  η : {I : Type₀} (M : Mnd I) → (i : I) → γ M i
  μ : {I : Type₀} (M : Mnd I) {i : I} (c : γ M i) (δ : (p : ρ M c) → γ M (τ M p)) → γ M i

  ηp : {I : Type₀} (M : Mnd I) (i : I) → ρ M (η M i)
  μρ : {I : Type₀} (M : Mnd I) {i : I} {c : γ M i}
       (δ : (p : ρ M c) → γ M (τ M p))
       (p₀ : ρ M c) (p₁ : ρ M (δ p₀)) → ρ M (μ M c δ)

  ηp-η : {I : Type₀} (M : Mnd I) (i : I) (p : ρ M (η M i)) → ηp M i == p

  μρ-fst : {I : Type₀} (M : Mnd I) {i : I} {c : γ M i}
           (δ : (p : ρ M c) → γ M (τ M p)) → ρ M (μ M c δ) → ρ M c

  μρ-snd : {I : Type₀} (M : Mnd I) {i : I} {c : γ M i}
           (δ : (p : ρ M c) → γ M (τ M p)) 
           (pp : ρ M (μ M c δ)) → ρ M (δ (μρ-fst M δ pp))

  postulate
  
    μρ-η : {I : Type₀} (M : Mnd I) {i : I} {c : γ M i}
           (δ : (p : ρ M c) → γ M (τ M p))
           (p : ρ M (μ M c δ)) → μρ M δ (μρ-fst M δ p) (μρ-snd M δ p) == p

    μρ-fst-β : {I : Type₀} (M : Mnd I) {i : I} {c : γ M i}
               (δ : (p : ρ M c) → γ M (τ M p))
               (p₀ : ρ M c) (p₁ : ρ M (δ p₀)) → 
               μρ-fst M δ (μρ M δ p₀ p₁) == p₀

    μρ-snd-β : {I : Type₀} (M : Mnd I) {i : I} {c : γ M i}
               (δ : (p : ρ M c) → γ M (τ M p))
               (p₀ : ρ M c) (p₁ : ρ M (δ p₀)) → 
               μρ-snd M δ (μρ M δ p₀ p₁) == p₁ [ (λ p → ρ M (δ p)) ↓ μρ-fst-β M δ p₀ p₁ ] 

  postulate
  
    ηp-compat : {I : Type₀} {M : Mnd I} (i : I) →
                τ M (ηp M i) ↦ i

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
             μ M (η M i) δ ↦ δ (ηp M i)

    {-# REWRITE unit-r #-}
    
    assoc : {I : Type₀} {M : Mnd I} {i : I} {c : γ M i}
            (δ : (p : ρ M c) → γ M (τ M p))
            (ε : (q : ρ M (μ M c δ)) → γ M (τ M q)) →
            μ M (μ M c δ) ε ↦ μ M c (λ p → μ M (δ p) (λ q → ε (μρ M δ p q))) 

    {-# REWRITE assoc #-}

  data Mnd where
    id : (I : Type₀) → Mnd I
    slc : {I : Type₀} (M : Mnd I) → Mnd (Σ I (γ M))
    -- pb : {I : Type₀} (M : Mnd I) (X : I → Type₀) → Mnd (Σ I X)

  -- The pullback monad
  -- module _ {I : Type₀} (M : Mnd I) (X : I → Type₀) where

  --   I-pb : Type₀
  --   I-pb = Σ I X

  --   γ-pb : I-pb → Type₀
  --   γ-pb (i , x) = Σ (γ M i) (λ c → (p : ρ M c) → X (τ M p))

  --   ρ-pb : {i : I-pb} → γ-pb i → Type₀
  --   ρ-pb {i , x} (c , δ) = ρ M c

  --   τ-pb : {i : I-pb} {c : γ-pb i} → ρ-pb {i = i} c → I-pb
  --   τ-pb {i , x} {c , δ} p = τ M p , δ p

  --   η-pb : (i : I-pb) → γ-pb i
  --   η-pb (i , x) = η M i , λ p → transport X (ap (τ M) (ηp-η M i p)) x

  --   ηp-pb : (i : I-pb) → ρ-pb {i = i} (η-pb i)
  --   ηp-pb (i , x) = ηp M i

  --   ηp-η-pb : (i : I-pb) (p : ρ-pb {i = i} (η-pb i)) → ηp-pb i == p
  --   ηp-η-pb (i , x) p = ηp-η M i p

  --   μ-pb : {i : I-pb} (c : γ-pb i) (ε : (p : ρ-pb {i = i} c) → γ-pb (τ-pb {i = i} {c = c} p)) → γ-pb i
  --   μ-pb {i , x} (c , δ) ε = μ M c (fst ∘ ε) , λ p → transport X (coh p) (ε' p)

  --     where coh : (p : ρ M (μ M c (fst ∘ ε))) → τ M (μρ-snd M (fst ∘ ε) p) == τ M p
  --           coh p = ap (τ M) (μρ-η M (fst ∘ ε) p)

  --           ε' : (p : ρ M (μ M c (fst ∘ ε))) → X (τ M (μρ-snd M (fst ∘ ε) p))
  --           ε' p = snd (ε (μρ-fst M (fst ∘ ε) p)) (μρ-snd M (fst ∘ ε) p)

  --   μρ-pb : {i : I-pb} {c : γ-pb i}
  --           (ε : (p : ρ-pb {i = i} c) → γ-pb (τ-pb {i = i} {c = c} p)) →
  --           (p₀ : ρ-pb {i = i} c) (p₁ : ρ-pb {i = τ-pb {i = i} {c = c} p₀} (ε p₀)) → 
  --           ρ-pb {i = i} (μ-pb {i = i} c ε)
  --   μρ-pb {i , x} {c , δ} ε = μρ M (fst ∘ ε)

  --   μρ-fst-pb : {i : I-pb} {c : γ-pb i}
  --               (ε : (p : ρ-pb {i = i} c) → γ-pb (τ-pb {i = i} {c = c} p)) →
  --               ρ-pb {i = i} (μ-pb {i = i} c ε) → ρ-pb {i = i} c
  --   μρ-fst-pb {i , x} {c , δ} ε q = μρ-fst M (fst ∘ ε) q

  --   μρ-snd-pb : {i : I-pb} {c : γ-pb i}
  --               (ε : (p : ρ-pb {i = i} c) → γ-pb (τ-pb {i = i} {c = c} p)) →
  --               (q : ρ-pb {i = i} (μ-pb {i = i} c ε)) →
  --               ρ-pb {i = τ-pb {i = i} {c = c} (μρ-fst-pb {i = i} {c = c} ε q)} (ε (μρ-fst-pb {i = i} {c = c} ε q))
  --   μρ-snd-pb {i , x} {c , δ} ε q = μρ-snd M (fst ∘ ε) q                

  -- The slice monad
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

    module Local {i : I} {c : γ M i}
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

    ηp-slc : (i : I-slc) → ρ-slc (η-slc i)
    ηp-slc (i , c) = inl unit
    
    ηp-η-slc : (i : I-slc) (p : ρ-slc (η-slc i)) → ηp-slc i == p
    ηp-η-slc (i , c) (inl unit) = idp
    ηp-η-slc (i , c) (inr (_ , ()))

    --
    --  Grafting, and the equivalence of places
    --
    
    slc-graft : {i : I} {c : γ M i} (n : Nst c)
                (δ : (p : ρ M c) → γ M (τ M p))
                (ε : (p : ρ M c) → Nst (δ p)) →
                Nst (μ M c δ)
    slc-graft (dot i) δ ε = ε (ηp M i)
    slc-graft (box c δ ε) δ₁ ε₁ = box c δ' (λ p → slc-graft (ε p) (δ₁' p) (ε₁' p))
      where open Local δ ε δ₁ ε₁

    slc-graft-ρ-to : {i : I} {c : γ M i} (n : Nst c)
                     (δ : (p : ρ M c) → γ M (τ M p))
                     (ε : (p : ρ M c) → Nst (δ p)) → 
                     ρ-slc n ⊔ Σ (ρ M c) (ρ-slc ∘ ε) → ρ-slc (slc-graft n δ ε)
    slc-graft-ρ-to (dot i) δ ε (inl ())
    slc-graft-ρ-to (box c δ ε) δ₁ ε₁ (inl (inl unit)) = inl unit
    slc-graft-ρ-to (box c δ ε) δ₁ ε₁ (inl (inr (p , q))) = inr (p , slc-graft-ρ-to (ε p) (δ₁' p) (ε₁' p) (inl q))
      where open Local δ ε δ₁ ε₁
    slc-graft-ρ-to (dot i) δ₁ ε₁ (inr (p , q)) = transport! (ρ-slc ∘ ε₁) (ηp-η M i p) q 
    slc-graft-ρ-to (box c δ ε) δ₁ ε₁ (inr (p , q)) = inr (p₀ , IH)
      where open Local δ ε δ₁ ε₁

            p₀ = μρ-fst M δ p
            p₁ = μρ-snd M δ p

            coh : μρ M δ p₀ p₁ == p
            coh = μρ-η M δ p 

            P : Σ (ρ M (μ M c δ)) (Nst ∘ δ₁) → Type₀
            P (r , n) = ρ-slc n

            IH : ρ-slc (slc-graft (ε p₀) (δ₁' p₀) (ε₁' p₀))
            IH = slc-graft-ρ-to (ε p₀) (δ₁' p₀) (ε₁' p₀) (inr (p₁ , (transport! P (pair= coh (apd ε₁ coh)) q)))

    slc-graft-ρ-from : {i : I} {c : γ M i} (n : Nst c)
                  (δ : (p : ρ M c) → (γ M (τ M p)))
                  (ε : (p : ρ M c) → Nst (δ p)) →
                  ρ-slc (slc-graft n δ ε) → ρ-slc n ⊔ Σ (ρ M c) (ρ-slc ∘ ε) 
    slc-graft-ρ-from (dot i) δ₁ ε₁ q = inr (ηp M i , q)
    slc-graft-ρ-from (box c δ ε) δ₁ ε₁ (inl unit) = inl (inl unit)
    slc-graft-ρ-from (box c δ ε) δ₁ ε₁ (inr (p , q)) with let open Local δ ε δ₁ ε₁ in slc-graft-ρ-from (ε p) (δ₁' p) (ε₁' p) q 
    slc-graft-ρ-from (box c δ ε) δ₁ ε₁ (inr (p , q)) | inl q₀ = inl (inr (p , q₀))
    slc-graft-ρ-from (box c δ ε) δ₁ ε₁ (inr (p , q)) | inr (p₀ , q₀) = inr (μρ M δ p p₀ , q₀)

    slc-graft-ρ-to-from : {i : I} {c : γ M i} (n : Nst c)
                          (δ : (p : ρ M c) → (γ M (τ M p)))
                          (ε : (p : ρ M c) → Nst (δ p))
                          (q : ρ-slc (slc-graft n δ ε)) →
                          slc-graft-ρ-to n δ ε (slc-graft-ρ-from n δ ε q) == q
    slc-graft-ρ-to-from (dot i) δ₁ ε₁ q = ap (λ e → transport! (ρ-slc ∘ ε₁) e q) coh

      where coh : ηp-η M i (ηp M i) == idp
            coh = fst (has-level-apply
                      (has-level-apply
                      (has-level-apply (dec-eq-is-set (ρ-dec M (η M i))) (ηp M i) (ηp M i))
                                                        (ηp-η M i (ηp M i)) idp))
            
    slc-graft-ρ-to-from (box c δ ε) δ₁ ε₁ (inl unit) = idp
    slc-graft-ρ-to-from (box c δ ε) δ₁ ε₁ (inr (p , q)) with
      slc-graft-ρ-from (ε p) (λ q → δ₁ (μρ M δ p q)) (λ q → ε₁ (μρ M δ p q)) q |
        inspect (slc-graft-ρ-from (ε p) (λ q → δ₁ (μρ M δ p q)) (λ q → ε₁ (μρ M δ p q))) q
        
    slc-graft-ρ-to-from (box c δ ε) δ₁ ε₁ (inr (p , q)) | inl q₀ | ingraph e = ap (λ q₁ → inr (p , q₁)) lem

      where open Local δ ε δ₁ ε₁

            lem = slc-graft-ρ-to (ε p) (δ₁' p) (ε₁' p) (inl q₀)
                    =⟨ ! e |in-ctx (λ q₁ → slc-graft-ρ-to (ε p) (δ₁' p) (ε₁' p) q₁) ⟩
                  slc-graft-ρ-to (ε p) (δ₁' p) (ε₁' p) (slc-graft-ρ-from (ε p) (δ₁' p) (ε₁' p) q)
                    =⟨ slc-graft-ρ-to-from (ε p) (δ₁' p) (ε₁' p) q ⟩ 
                  q ∎
                  
    slc-graft-ρ-to-from (box c δ ε) δ₁ ε₁ (inr (p , q)) | inr (p₀ , q₀) | ingraph e = lem

      where open Local δ ε δ₁ ε₁

            r₀ = μρ-fst M δ (μρ M δ p p₀)
            r₁ = μρ-snd M δ (μρ M δ p p₀)

            coh = μρ-η M δ (μρ M δ p p₀)
            
            P : Σ (ρ M (μ M c δ)) (Nst ∘ δ₁) → Type₀
            P (r , n) = ρ-slc n

            lem = inr (r₀ , slc-graft-ρ-to (ε r₀) (δ₁' r₀) (ε₁' r₀) (inr (r₁ , (transport! P (pair= coh (apd ε₁ coh)) q₀)))) =⟨ {!e!} ⟩
                  inr (p , q) ∎


    -- μρ-η : {I : Type₀} (M : Mnd I) {i : I} {c : γ M i}
    --        (δ : (p : ρ M c) → γ M (τ M p))
    --        (p : ρ M (μ M c δ)) → μρ M δ (μρ-fst M δ p) (μρ-snd M δ p) == p

            -- IH : slc-graft-ρ-to (ε p) (δ₁' p) (ε₁' p) (slc-graft-ρ-from (ε p) (δ₁' p) (ε₁' p) q) == q
            -- IH = slc-graft-ρ-to-from (ε p) (δ₁' p) (ε₁' p) q 

    --
    --  Joining, and the equivalence of places
    --

    μ-slc : {i : I-slc} (c : γ-slc i) (δ : (p : ρ-slc c) → γ-slc (τ-slc p)) → γ-slc i
    μ-slc (dot i) κ = dot i
    μ-slc (box c δ ε) κ = slc-graft (κ (inl unit)) δ (λ p → μ-slc (ε p) (λ q → κ (inr (p , q))))

    μρ-slc : {i : I-slc} {c : γ-slc i}
             (κ : (p : ρ-slc c) → γ-slc (τ-slc p)) 
             (p₀ : ρ-slc c) (p₁ : ρ-slc (κ p₀)) → 
             ρ-slc (μ-slc c κ)
    μρ-slc {c = dot i} κ () _
    μρ-slc {c = box c δ ε} κ (inl unit) q =
      slc-graft-ρ-to (κ (inl unit)) δ (λ p → μ-slc (ε p) (λ q₀ → κ (inr (p , q₀)))) (inl q)
    μρ-slc {c = box c δ ε} κ (inr (p , q₀)) q =
      slc-graft-ρ-to (κ (inl unit)) δ (λ p₁ → μ-slc (ε p₁) (λ q₁ → κ (inr (p₁ , q₁)))) (inr (p , μρ-slc (λ q₁ → κ (inr (p , q₁))) q₀ q))

    μρ-fst-slc : {i : I-slc} {c : γ-slc i}
                 (κ : (q : ρ-slc c) → γ-slc (τ-slc q))
                 (q : ρ-slc (μ-slc c κ)) → ρ-slc c
    μρ-fst-slc {c = dot i} κ ()
    μρ-fst-slc {c = box c δ ε} κ q with slc-graft-ρ-from (κ (inl unit)) δ (λ q₀ → μ-slc (ε q₀) (λ q₁ → κ (inr (q₀ , q₁)))) q
    μρ-fst-slc {c = box c δ ε} κ q | inl q₀ = inl unit
    μρ-fst-slc {c = box c δ ε} κ q | inr (p , q₀) = inr (p , μρ-fst-slc {c = ε p} (λ q₁ → κ (inr (p , q₁))) q₀)
             
    μρ-snd-slc : {i : I-slc} {c : γ-slc i}
                 (κ : (q : ρ-slc c) → γ-slc (τ-slc q))
                 (q : ρ-slc (μ-slc c κ)) → ρ-slc (κ (μρ-fst-slc κ q))
    μρ-snd-slc {c = dot i} κ ()
    μρ-snd-slc {c = box c δ ε} κ q with slc-graft-ρ-from (κ (inl unit)) δ (λ q₀ → μ-slc (ε q₀) (λ q₁ → κ (inr (q₀ , q₁)))) q
    μρ-snd-slc {c = box c δ ε} κ q | inl q₀ = q₀
    μρ-snd-slc {c = box c δ ε} κ q | inr (p , q₀) = μρ-snd-slc {c = ε p} (λ q₁ → κ (inr (p , q₁))) q₀

    μρ-η-slc : {i : I-slc} {c : γ-slc i}
               (κ : (q : ρ-slc c) → γ-slc (τ-slc q))
               (q : ρ-slc (μ-slc c κ)) →
               μρ-slc κ (μρ-fst-slc κ q) (μρ-snd-slc κ q) == q
    μρ-η-slc {c = dot i} κ ()
    μρ-η-slc {c = box c δ ε} κ q with slc-graft-ρ-from (κ (inl unit)) δ (λ q₀ → μ-slc (ε q₀) (λ q₁ → κ (inr (q₀ , q₁)))) q
                                      | inspect (slc-graft-ρ-from (κ (inl unit)) δ (λ q₀ → μ-slc (ε q₀) (λ q₁ → κ (inr (q₀ , q₁))))) q
    μρ-η-slc {c = box c δ ε} κ q | inl q₀ | ingraph e = lem
    
      where c' = (κ (inl unit))
            ε' = (λ p → μ-slc (ε p) (λ q₁ → κ (inr (p , q₁))))

            lem : slc-graft-ρ-to  c' δ  ε' (inl q₀) == q
            lem = slc-graft-ρ-to c' δ ε' (inl q₀) =⟨ ap (slc-graft-ρ-to c' δ ε') (! e) ⟩
                  slc-graft-ρ-to c' δ ε' (slc-graft-ρ-from c' δ ε' q) =⟨ slc-graft-ρ-to-from c' δ ε' q ⟩ 
                  q ∎
    
    μρ-η-slc {c = box c δ ε} κ q | inr (p , q₀) | ingraph e = lem

      where c' = (κ (inl unit))
            ε' = (λ p → μ-slc (ε p) (λ q₁ → κ (inr (p , q₁))))
            κ' = (λ q₁ → κ (inr (p , q₁)))
            
            IH : μρ-slc κ' (μρ-fst-slc κ' q₀) (μρ-snd-slc κ' q₀) == q₀
            IH = μρ-η-slc κ' q₀

            lem = slc-graft-ρ-to c' δ ε' (inr (p , μρ-slc κ' (μρ-fst-slc κ' q₀) (μρ-snd-slc κ' q₀)))
                    =⟨ IH |in-ctx (λ q₁ → slc-graft-ρ-to c' δ ε' (inr (p , q₁))) ⟩
                  slc-graft-ρ-to c' δ ε' (inr (p , q₀))
                    =⟨ ap (slc-graft-ρ-to c' δ ε') (! e) ⟩ 
                  slc-graft-ρ-to c' δ ε' (slc-graft-ρ-from c' δ ε' q)
                    =⟨ slc-graft-ρ-to-from c' δ ε' q ⟩ 
                  q ∎

  -- Now we finish the decoding functions

  γ (id I) i = ⊤
  γ (slc M) = γ-slc M
  -- γ (pb M X) = γ-pb M X

  ρ (id I) unit = ⊤
  ρ (slc M) = ρ-slc M
  -- ρ (pb M X) {i = i} = ρ-pb M X {i = i}

  τ (id I) {i} unit = i
  τ (slc M) = τ-slc M
  -- τ (pb M X) {i = i} {c = c} = τ-pb M X {i = i} {c = c}

  η (id I) _ = unit
  η (slc M) = η-slc M
  -- η (pb M X) = η-pb M X

  μ (id I) unit _ = unit
  μ (slc M) = μ-slc M
  -- μ (pb M X) {i = i} = μ-pb M X {i = i}

  ηp (id I) _ = unit
  ηp (slc M) = ηp-slc M
  -- ηp (pb M X) = ηp-pb M X

  μρ (id I) _ _ _ = unit
  μρ (slc M) = μρ-slc M
  -- μρ (pb M X) {i = i} {c = c} = μρ-pb M X {i = i} {c = c}

  ηp-η (id I) i unit = idp
  ηp-η (slc M) = ηp-η-slc M
  -- ηp-η (pb M X) = ηp-η-pb M X

  μρ-fst (id I) _ _ = unit
  μρ-fst (slc M) = μρ-fst-slc M
  -- μρ-fst (pb M X) {i = i} {c = c} = μρ-fst-pb M X {i = i} {c = c}
  
  μρ-snd (id I) _ _ = unit
  μρ-snd (slc M) = μρ-snd-slc M
  -- μρ-snd (pb M X) {i = i} {c = c} = μρ-snd-pb M X {i = i} {c = c}
  
