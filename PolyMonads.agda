{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Poly 
open import Inspect

module PolyMonads where

  data Mnd : Type₀ → Type₁

  γ : {I : Type₀} (M : Mnd I) → I → Type₀
  ρ : {I : Type₀} (M : Mnd I) (i : I) → γ M i → Type₀
  τ : {I : Type₀} (M : Mnd I) (i : I) (c : γ M i) → ρ M i c → I

  η : {I : Type₀} (M : Mnd I) (i : I) → γ M i
  μ : {I : Type₀} (M : Mnd I) (i : I) (c : γ M i) (δ : (p : ρ M i c) → γ M (τ M i c p)) → γ M i

  ηρ-contr : {I : Type₀} (M : Mnd I) (i : I) → is-contr (ρ M i (η M i))
  μρ-equiv : {I : Type₀} (M : Mnd I) (i : I) (c : γ M i)
             (δ : (p : ρ M i c) → γ M (τ M i c p)) →
             Σ (ρ M i c) (λ p → ρ M (τ M i c p) (δ p)) ≃' ρ M i (μ M i c δ)

  ⟪_⟫ : {I : Type₀} (M : Mnd I) → (I → Type₀) → I → Type₀
  ⟪ M ⟫ X i = Σ (γ M i) (λ c → (p : ρ M i c) → X (τ M i c p))

  module _ {I : Type₀} (M : Mnd I) where
  
    ηρ : (i : I) → ρ M i (η M i)
    ηρ i = fst (has-level-apply (ηρ-contr M i))

    ηρ-η : (i : I) (p : ρ M i (η M i)) → ηρ i == p
    ηρ-η i p = snd (has-level-apply (ηρ-contr M i)) p

    ηρ-η-coh : (i : I) → ηρ-η i (ηρ i) == idp
    ηρ-η-coh i = contr-has-all-paths
                   {{has-level-apply (raise-level ⟨-2⟩ (ηρ-contr M i)) (ηρ i) (ηρ i)}}
                   (ηρ-η i (ηρ i)) idp

    μρ : (i : I) (c : γ M i)
      → (δ : (p : ρ M i c) → γ M (τ M i c p)) 
      → (p₀ : ρ M i c) (p₁ : ρ M (τ M i c p₀) (δ p₀))
      → ρ M i (μ M i c δ)
    μρ i c δ p₀ p₁ = fst (μρ-equiv M i c δ) (p₀ , p₁)

    μρ-fst : (i : I) (c : γ M i)
      → (δ : (p : ρ M i c) → γ M (τ M i c p)) → ρ M i (μ M i c δ)
      → ρ M i c
    μρ-fst i c δ p = fst (is-equiv'.g (snd (μρ-equiv M i c δ)) p)

    μρ-snd : (i : I) (c : γ M i)
      → (δ : (p : ρ M i c) → γ M (τ M i c p)) 
      → (pp : ρ M i (μ M i c δ))
      → ρ M (τ M i c (μρ-fst i c δ pp)) (δ (μρ-fst i c δ pp))
    μρ-snd i c δ p = snd (is-equiv'.g (snd (μρ-equiv M i c δ)) p)

    μρ-η : (i : I) (c : γ M i)
      → (δ : (p : ρ M i c) → γ M (τ M i c p))
      → (p : ρ M i (μ M i c δ))
      → μρ i c δ (μρ-fst i c δ p) (μρ-snd i c δ p) == p
    μρ-η i c δ p = is-equiv'.f-g (snd (μρ-equiv M i c δ)) p

    μρ-β : (i : I) (c : γ M i)
      → (δ : (p : ρ M i c) → γ M (τ M i c p))
      → (p₀ : ρ M i c) → (p₁ : ρ M (τ M i c p₀) (δ p₀)) 
      → is-equiv'.g (snd (μρ-equiv M i c δ)) (μρ i c δ p₀ p₁) == (p₀ , p₁)
    μρ-β i c δ p₀ p₁ = is-equiv'.g-f (snd (μρ-equiv M i c δ)) (p₀ , p₁)

    μρ-fst-β : (i : I) (c : γ M i)
      → (δ : (p : ρ M i c) → γ M (τ M i c p))
      → (p₀ : ρ M i c) (p₁ : ρ M (τ M i c p₀) (δ p₀)) 
      → μρ-fst i c δ (μρ i c δ p₀ p₁) == p₀
    μρ-fst-β i c δ p₀ p₁ = fst= (μρ-β i c δ p₀ p₁) 
  
    μρ-snd-β : (i : I) (c : γ M i)
      → (δ : (p : ρ M i c) → γ M (τ M i c p))
      → (p₀ : ρ M i c) (p₁ : ρ M (τ M i c p₀) (δ p₀)) 
      → μρ-snd i c δ (μρ i c δ p₀ p₁) == p₁ [ (λ p → ρ M (τ M i c p) (δ p)) ↓ μρ-fst-β i c δ p₀ p₁ ] 
    μρ-snd-β i c δ p₀ p₁ = snd= (μρ-β i c δ p₀ p₁) 

    μρ-η-coh : (i : I) (c : γ M i)
      → (δ : (p : ρ M i c) → γ M (τ M i c p))
      → (p₀ : ρ M i c) (p₁ : ρ M (τ M i c p₀) (δ p₀))
      → ap (fst (μρ-equiv M i c δ)) (pair= (μρ-fst-β i c δ p₀ p₁) (μρ-snd-β i c δ p₀ p₁))
        == μρ-η i c δ (μρ i c δ p₀ p₁)
    μρ-η-coh i c δ p₀ p₁ =
      transport (λ x → ap (fst (μρ-equiv M i c δ)) x == μρ-η i c δ (μρ i c δ p₀ p₁))
                (pair=-η (is-equiv'.g-f (snd (μρ-equiv M i c δ)) (p₀ , p₁)))
                (is-equiv'.adj (snd (μρ-equiv M i c δ)) (p₀ , p₁))

    postulate

      ηp-compat : (i : I) 
        → τ M i (η M i) (ηρ i) ↦ i

      {-# REWRITE ηp-compat #-}

      μρ-compat : (i : I) (c : γ M i)
        → (δ : (p : ρ M i c) → γ M (τ M i c p))
        → (p₀ : ρ M i c) (p₁ : ρ M (τ M i c p₀) (δ p₀)) → ρ M i (μ M i c δ) 
        → τ M i (μ M i c δ ) (μρ i c δ p₀ p₁) ↦ τ M (τ M i c p₀) (δ p₀) p₁

      {-# REWRITE μρ-compat #-}

      unit-l : (i : I) (c : γ M i) 
        → μ M i c (λ p → η M (τ M i c p)) ↦ c

      {-# REWRITE unit-l #-}

      unit-r : (i : I)
        → (δ : (p : ρ M i (η M i)) → γ M (τ M i (η M i) p)) 
        → μ M i (η M i) δ ↦ δ (ηρ i)

      {-# REWRITE unit-r #-}

      assoc : (i : I) (c : γ M i)
              (δ : (p : ρ M i c) → γ M (τ M i c p))
              (ε : (q : ρ M i (μ M i c δ)) → γ M (τ M i (μ M i c δ) q)) →
              μ M i (μ M i c δ) ε ↦ μ M i c (λ p → μ M (τ M i c p) (δ p) (λ q → ε (μρ i c δ p q))) 

      {-# REWRITE assoc #-}

    μρ-snd-coh : (i : I) (c : γ M i)
      → (δ : (p : ρ M i c) → γ M (τ M i c p))
      → (p : ρ M i (μ M i c δ))
      → τ M (τ M i c (μρ-fst i c δ p)) (δ (μρ-fst i c δ p)) (μρ-snd i c δ p)
        == τ M i (μ M i c δ) p
    μρ-snd-coh i c δ p = ap (τ M i (μ M i c δ)) (μρ-η i c δ p) 

  --
  --  The pullback monad
  --
  
  module _ {I : Type₀} (M : Mnd I) (X : I → Type₀) where

    I-pb : Type₀
    I-pb = Σ I X

    γ-pb : I-pb → Type₀
    γ-pb (i , x) = Σ (γ M i) (λ c → (p : ρ M i c) → X (τ M i c p))

    ρ-pb : (i : I-pb) → γ-pb i → Type₀
    ρ-pb (i , x) (c , δ) = ρ M i c

    τ-pb : (i : I-pb) (c : γ-pb i) → ρ-pb i c → I-pb
    τ-pb (i , x) (c , δ) p = τ M i c p , δ p

    η-pb : (i : I-pb) → γ-pb i
    η-pb (i , x) = η M i , λ p → transport X (ap (τ M i (η M i)) (ηρ-η M i p)) x

    ηρ-contr-pb : (i : I-pb) → is-contr (ρ-pb i (η-pb i))
    ηρ-contr-pb (i , x) = ηρ-contr M i

    μ-pb : (i : I-pb) (c : γ-pb i) (ε : (p : ρ-pb i c) → γ-pb (τ-pb i c p)) → γ-pb i
    μ-pb (i , x) (c , δ) ε =
      let coh p = ap (τ M i (μ M i c (fst ∘ ε))) (μρ-η M i c (fst ∘ ε) p)
          ε' p = snd (ε (μρ-fst M i c (fst ∘ ε) p)) (μρ-snd M i c (fst ∘ ε) p)
      in μ M i c (fst ∘ ε) , λ p → transport X (coh p) (ε' p)

    μρ-equiv-pb : (i : I-pb) (c : γ-pb i)
      → (ε : (p : ρ-pb i c) → γ-pb (τ-pb i c p))
      → Σ (ρ-pb i c) (λ p → ρ-pb (τ-pb i c p) (ε p))
        ≃' ρ-pb i (μ-pb i c ε)
    μρ-equiv-pb (i , x) (c , δ) ε = μρ-equiv M i c (fst ∘ ε)

  --
  -- The slice monad
  --
  
  module _ {I : Type₀} (M : Mnd I) where

    I-slc : Type₀
    I-slc = Σ I (γ M)

    data Nst : (i : I) → (c : γ M i) → Type₀ where
      dot : (i : I) → Nst i (η M i)
      box : (i : I) (c : γ M i)
            (δ : (p : ρ M i c) → γ M (τ M i c p))
            (ε : (p : ρ M i c) → Nst (τ M i c p) (δ p)) →
            Nst i (μ M i c δ)

    γ-slc : I-slc → Type₀
    γ-slc (i , c) = Nst i c
    
    ρ-slc : (i : I-slc) (n : γ-slc i) → Type₀
    ρ-slc (i , .(η M i)) (dot .i) = ⊥
    ρ-slc (i , .(μ M i c δ)) (box .i c δ ε) = ⊤ ⊔ Σ (ρ M i c) (λ p → ρ-slc (τ M i c p , δ p) (ε p))

    τ-slc : (i : I-slc) (n : γ-slc i) (p : ρ-slc i n) → I-slc
    τ-slc (i , .(η M i)) (dot .i) ()
    τ-slc (i , .(μ M i c δ)) (box .i c δ ε) (inl unit) = i , c
    τ-slc (i , .(μ M i c δ)) (box .i c δ ε) (inr (p , q)) = τ-slc (τ M i c p , δ p) (ε p) q

    η-slc : (i : I-slc) → γ-slc i
    η-slc (i , c) = (box i c (λ p → η M (τ M i c p)) (λ p → dot (τ M i c p)))

    ηρ-slc : (i : I-slc) → ρ-slc i (η-slc i)
    ηρ-slc (i , c) = inl unit
    
    ηρ-η-slc : (i : I-slc) (p : ρ-slc i (η-slc i)) → ηρ-slc i == p
    ηρ-η-slc (i , c) (inl unit) = idp
    ηρ-η-slc (i , c) (inr (_ , ()))

    ηρ-contr-slc : (i : I-slc) → is-contr (ρ-slc i (η-slc i))
    ηρ-contr-slc i = has-level-in (ηρ-slc i , ηρ-η-slc i)

    --
    --  Grafting, and the associated equivalence of places
    --
    
    graft-slc : (i : I) (c : γ M i) (n : Nst i c)
      → (δ₁ : (p : ρ M i c) → γ M (τ M i c p))
      → (ε₁ : (p : ρ M i c) → Nst (τ M i c p) (δ₁ p)) 
      → Nst i (μ M i c δ₁)
    graft-slc i .(η M i) (dot .i) δ₁ ε₁ = ε₁ (ηρ M i)
    graft-slc i .(μ M i c δ) (box .i c δ ε) δ₁ ε₁ =
      let  δ₁' p q = δ₁ (μρ M i c δ p q)
           ε₁' p q = ε₁ (μρ M i c δ p q)
           δ' p = μ M (τ M i c p) (δ p) (δ₁' p)
      in box i c δ' (λ p → graft-slc (τ M i c p) (δ p) (ε p) (δ₁' p) (ε₁' p))

    graft-slc-ρ-to : (i : I) (c : γ M i) (n : Nst i c)
      → (δ₁ : (p : ρ M i c) → γ M (τ M i c p))
      → (ε₁ : (p : ρ M i c) → Nst (τ M i c p) (δ₁ p)) 
      → ρ-slc (i , c) n ⊔ Σ (ρ M i c) (λ p → ρ-slc (τ M i c p , δ₁ p) (ε₁ p))
      → ρ-slc (i , μ M i c δ₁) (graft-slc i c n δ₁ ε₁)
    graft-slc-ρ-to i .(η M i) (dot .i) δ₁ ε₁ (inl ())
    graft-slc-ρ-to i .(η M i) (dot .i) δ₁ ε₁ (inr (p , q)) = 
      transport! (λ p → ρ-slc (τ M i (η M i) p , δ₁ p) (ε₁ p)) (ηρ-η M i p) q
    graft-slc-ρ-to i .(μ M i c δ) (box .i c δ ε) δ₁ ε₁ (inl (inl unit)) = inl unit
    graft-slc-ρ-to i .(μ M i c δ) (box .i c δ ε) δ₁ ε₁ (inl (inr (p , q))) = 
      let  δ₁' p q = δ₁ (μρ M i c δ p q)
           ε₁' p q = ε₁ (μρ M i c δ p q)
           δ' p = μ M (τ M i c p) (δ p) (δ₁' p)
      in inr (p , graft-slc-ρ-to (τ M i c p) (δ p) (ε p) (δ₁' p) (ε₁' p) (inl q))
    graft-slc-ρ-to i .(μ M i c δ) (box .i c δ ε) δ₁ ε₁ (inr (p , q)) = 
      let  δ₁' p q = δ₁ (μρ M i c δ p q)
           ε₁' p q = ε₁ (μρ M i c δ p q)
           δ' p = μ M (τ M i c p) (δ p) (δ₁' p)
           p₀ = μρ-fst M i c δ p
           p₁ = μρ-snd M i c δ p
           coh = μρ-η M i c δ p
           ρ-slc' pn = ρ-slc (τ M i (μ M i c δ) (fst pn) , δ₁ (fst pn)) (snd pn)
           q' = transport! ρ-slc' (pair= coh (apd ε₁ coh)) q
      in inr (p₀ , graft-slc-ρ-to (τ M i c p₀) (δ p₀) (ε p₀) (δ₁' p₀) (ε₁' p₀) (inr (p₁ , q')))

    graft-slc-ρ-from : (i : I) (c : γ M i) (n : Nst i c)
      → (δ₁ : (p : ρ M i c) → γ M (τ M i c p))
      → (ε₁ : (p : ρ M i c) → Nst (τ M i c p) (δ₁ p))
      → ρ-slc (i , μ M i c δ₁) (graft-slc i c n δ₁ ε₁)
      → ρ-slc (i , c) n ⊔ Σ (ρ M i c) (λ p → ρ-slc (τ M i c p , δ₁ p) (ε₁ p))

    graft-slc-ρ-from-lcl : (i : I) (c : γ M i)
      → (δ : (p : ρ M i c) → γ M (τ M i c p))
      → (ε : (p : ρ M i c) → Nst (τ M i c p) (δ p))
      → (δ₁ : (p : ρ M i (μ M i c δ)) → γ M (τ M i (μ M i c δ) p))
      → (ε₁ : (p : ρ M i (μ M i c δ)) → Nst (τ M i (μ M i c δ) p) (δ₁ p))
      → (p : ρ M i c)
      → ρ-slc (τ M i c p , δ p) (ε p) ⊔
          Σ (ρ M (τ M i c p) (δ p)) (λ p₁ → ρ-slc (τ M (τ M i c p) (δ p) p₁ , δ₁ (μρ M i c δ p p₁)) (ε₁ (μρ M i c δ p p₁)))
      → (⊤ ⊔ Σ (ρ M i c) (λ p₁ → ρ-slc (τ M i c p₁ , δ p₁) (ε p₁))) ⊔
          Σ (ρ M i (μ M i c δ)) (λ p₁ → ρ-slc (τ M i (μ M i c δ) p₁ , δ₁ p₁) (ε₁ p₁))

    graft-slc-ρ-from i .(η M i) (dot .i) δ₁ ε₁ q = inr (ηρ M i , q)
    graft-slc-ρ-from i .(μ M i c δ) (box .i c δ ε) δ₁ ε₁ (inl unit) = inl (inl unit)
    graft-slc-ρ-from i .(μ M i c δ) (box .i c δ ε) δ₁ ε₁ (inr (p , q)) = 
      let  δ₁' p q = δ₁ (μρ M i c δ p q)
           ε₁' p q = ε₁ (μρ M i c δ p q)
           δ' p = μ M (τ M i c p) (δ p) (δ₁' p)
      in graft-slc-ρ-from-lcl i c δ ε δ₁ ε₁ p (graft-slc-ρ-from (τ M i c p) (δ p) (ε p) (δ₁' p) (ε₁' p) q) 

    graft-slc-ρ-from-lcl i c δ ε δ₁ ε₁ p (inl q₀) = inl (inr (p , q₀))
    graft-slc-ρ-from-lcl i c δ ε δ₁ ε₁ p (inr (p₀ , q₀)) = inr (μρ M i c δ p p₀ , q₀)

    graft-slc-ρ-to-from : (i : I) (c : γ M i) (n : Nst i c)
      → (δ₁ : (p : ρ M i c) → γ M (τ M i c p))
      → (ε₁ : (p : ρ M i c) → Nst (τ M i c p) (δ₁ p))
      → (q : ρ-slc (i , μ M i c δ₁) (graft-slc i c n δ₁ ε₁)) 
      → graft-slc-ρ-to i c n δ₁ ε₁ (graft-slc-ρ-from i c n δ₁ ε₁ q) == q

    graft-slc-ρ-to-from-lcl : (i : I) (c : γ M i)
      → (δ : (p : ρ M i c) → γ M (τ M i c p))
      → (ε : (p : ρ M i c) → Nst (τ M i c p) (δ p))
      → (δ₁ : (p : ρ M i (μ M i c δ)) → γ M (τ M i (μ M i c δ) p))
      → (ε₁ : (p : ρ M i (μ M i c δ)) → Nst (τ M i (μ M i c δ) p) (δ₁ p))
      → (p : ρ M i c)
      → (q : ρ-slc (τ M i c p , μ M (τ M i c p) (δ p) (λ q₁ → δ₁ (fst (μρ-equiv M i c δ) (p , q₁))))
                 (graft-slc (τ M i c p) (δ p) (ε p)
                   (λ q₁ → δ₁ (fst (μρ-equiv M i c δ) (p , q₁)))
                   (λ q₁ → ε₁ (fst (μρ-equiv M i c δ) (p , q₁))))) 
      → (q' : ρ-slc (τ M i c p , δ p) (ε p) ⊔
                Σ (ρ M (τ M i c p) (δ p)) (λ p₁ →
                  ρ-slc (τ M (τ M i c p) (δ p) p₁ , δ₁ (μρ M i c δ p p₁))
                  (ε₁ (μρ M i c δ p p₁))))
      → (e : q' == graft-slc-ρ-from (τ M i c p) (δ p) (ε p)
                     (λ q → δ₁ (μρ M i c δ p q))
                     (λ q → ε₁ (μρ M i c δ p q)) q)
      → graft-slc-ρ-to i (μ M i c δ) (box i c δ ε) δ₁ ε₁
        (graft-slc-ρ-from-lcl i c δ ε δ₁ ε₁ p q')
        == inr (p , q)

    graft-slc-ρ-to-from i .(η M i) (dot .i) δ₁ ε₁ q =
      let ρ-slc-ε₁ q = ρ-slc (τ M i (η M i) q , δ₁ q) (ε₁ q)
      in ap (λ e → transport! ρ-slc-ε₁ e q) (ηρ-η-coh M i)
    graft-slc-ρ-to-from i .(μ M i c δ) (box .i c δ ε) δ₁ ε₁ (inl unit) = idp
    graft-slc-ρ-to-from i .(μ M i c δ) (box .i c δ ε) δ₁ ε₁ (inr (p , q)) = 
      let  δ₁' p q = δ₁ (μρ M i c δ p q)
           ε₁' p q = ε₁ (μρ M i c δ p q)
           δ' p = μ M (τ M i c p) (δ p) (δ₁' p)
           frm = graft-slc-ρ-from (τ M i c p) (δ p) (ε p)
                   (λ q → δ₁ (μρ M i c δ p q))
                   (λ q → ε₁ (μρ M i c δ p q)) q
      in graft-slc-ρ-to-from-lcl i c δ ε δ₁ ε₁ p q frm idp

    graft-slc-ρ-to-from-lcl i c δ ε δ₁ ε₁ p q (inl q₀) e =
      let  δ₁' p q = δ₁ (μρ M i c δ p q)
           ε₁' p q = ε₁ (μρ M i c δ p q)
           δ' p = μ M (τ M i c p) (δ p) (δ₁' p)
           ih = graft-slc-ρ-to-from (τ M i c p) (δ p) (ε p) (δ₁' p) (ε₁' p) q
           lem = graft-slc-ρ-to (τ M i c p) (δ p) (ε p) (δ₁' p) (ε₁' p) (inl q₀)
                   =⟨ e |in-ctx (λ q₁ → graft-slc-ρ-to (τ M i c p) (δ p) (ε p) (δ₁' p) (ε₁' p) q₁) ⟩
                 graft-slc-ρ-to (τ M i c p) (δ p) (ε p) (δ₁' p) (ε₁' p)
                   (graft-slc-ρ-from (τ M i c p) (δ p) (ε p) (δ₁' p) (ε₁' p) q)
                   =⟨ ih ⟩
                 q ∎
      in ap (λ x → inr (p , x)) lem 
    graft-slc-ρ-to-from-lcl i c δ ε δ₁ ε₁ p q (inr (p₀ , q₀)) e = 
      let  δ₁' p q = δ₁ (μρ M i c δ p q)
           ε₁' p q = ε₁ (μρ M i c δ p q)
           δ' p = μ M (τ M i c p) (δ p) (δ₁' p)
           r₀ = μρ-fst M i c δ (μρ M i c δ p p₀)
           r₁ = μρ-snd M i c δ (μρ M i c δ p p₀)
           coh = μρ-η M i c δ (μρ M i c δ p p₀)
           α = pair= coh (apd ε₁ coh)
           β = pair= (μρ-fst-β M i c δ p p₀) (μρ-snd-β M i c δ p p₀)
           ρ-slc-ε₁ q₁ = ρ-slc (τ M i (μ M i c δ) q₁ , δ₁ q₁) (ε₁ q₁)
           ρ-slc-snd pn = ρ-slc (τ M i (μ M i c δ) (fst pn) , δ₁ (fst pn)) (snd pn)
           lem₀ = to-transp-↓ ρ-slc-snd α q₀
           lem₁ = ↓-apd-lem (curry ρ-slc-snd) ε₁ coh lem₀
           lem₂ = transport! (λ x → transport! ρ-slc-snd α q₀ == q₀ [ ρ-slc-ε₁ ↓ x ]) (μρ-η-coh M i c δ p p₀) lem₁
           lem₃ = ↓-ap-out (ρ-slc-ε₁) (fst (μρ-equiv M i c δ)) β lem₂
           gs-to x y = graft-slc-ρ-to (τ M i c x) (δ x) (ε x) (δ₁' x) (ε₁' x) y
           lem = (r₀ , gs-to r₀ (inr (r₁ , (transport! (ρ-slc-snd) α q₀))))
                   =⟨ pair= (μρ-fst-β M i c δ p p₀) (apd↓-cst (λ {x} y → gs-to x (inr y)) (↓-Σ-in (μρ-snd-β M i c δ p p₀) lem₃)) ⟩ 
                 (p , gs-to p (inr (p₀ , q₀)))
                   =⟨ e |in-ctx (λ y → (p , gs-to p y)) ⟩
                 (p , gs-to p (graft-slc-ρ-from (τ M i c p) (δ p) (ε p) (δ₁' p) (ε₁' p) q))
                   =⟨ ap (λ x → (p , x)) (graft-slc-ρ-to-from (τ M i c p) (δ p) (ε p) (δ₁' p) (ε₁' p) q) ⟩ 
                 (p , q) ∎
      in ap inr lem

    graft-slc-ρ-from-to : (i : I) (c : γ M i) (n : Nst i c)
      → (δ₁ : (p : ρ M i c) → γ M (τ M i c p))
      → (ε₁ : (p : ρ M i c) → Nst (τ M i c p) (δ₁ p))
      → (q : ρ-slc (i , c) n ⊔ Σ (ρ M i c) (λ p → ρ-slc (τ M i c p , δ₁ p) (ε₁ p)))
      → graft-slc-ρ-from i c n δ₁ ε₁ (graft-slc-ρ-to i c n δ₁ ε₁ q) == q

    graft-slc-ρ-from-to-lcl₀ : (i : I) (c : γ M i)
      → (δ : (p : ρ M i c) → γ M (τ M i c p))
      → (ε : (p : ρ M i c) → Nst (τ M i c p) (δ p))
      → (δ₁ : (p : ρ M i (μ M i c δ)) → γ M (τ M i (μ M i c δ) p))
      → (ε₁ : (p : ρ M i (μ M i c δ)) → Nst (τ M i (μ M i c δ) p) (δ₁ p))
      → (p : ρ M i c) (q : ρ-slc (τ M i c p , δ p) (ε p)) 
      → (q' : ρ-slc (τ M i c p , δ p) (ε p) ⊔ Σ (ρ M (τ M i c p) (δ p))
                (λ p₁ → ρ-slc (τ M (τ M i c p) (δ p) p₁ , 
                   δ₁ (μρ M i c δ p p₁)) (ε₁ (μρ M i c δ p p₁))))
      → (e : q' == (graft-slc-ρ-from (τ M i c p) (δ p) (ε p)
                     (λ q₁ → δ₁ (μρ M i c δ p q₁))
                     (λ q₁ → ε₁ (μρ M i c δ p q₁))
                       (graft-slc-ρ-to (τ M i c p) (δ p) (ε p)
                         (λ q₁ → δ₁ (μρ M i c δ p q₁))
                         (λ q₁ → ε₁ (μρ M i c δ p q₁)) (inl q))))
      → graft-slc-ρ-from-lcl i c δ ε δ₁ ε₁ p q' == inl (inr (p , q))

    graft-slc-ρ-from-to-lcl₁ : (i : I) (c : γ M i)
      → (δ : (p : ρ M i c) → γ M (τ M i c p))
      → (ε : (p : ρ M i c) → Nst (τ M i c p) (δ p))
      → (δ₁ : (p : ρ M i (μ M i c δ)) → γ M (τ M i (μ M i c δ) p))
      → (ε₁ : (p : ρ M i (μ M i c δ)) → Nst (τ M i (μ M i c δ) p) (δ₁ p))
      → (p : ρ M i (μ M i c δ)) (q : ρ-slc (τ M i (μ M i c δ) p , δ₁ p) (ε₁ p))
      → (q' : ρ-slc (τ M i c (μρ-fst M i c δ p) , δ (μρ-fst M i c δ p)) (ε (μρ-fst M i c δ p)) ⊔
                Σ (ρ M (τ M i c (μρ-fst M i c δ p)) (δ (μρ-fst M i c δ p)))
                  (λ p₁ → ρ-slc (τ M (τ M i c (μρ-fst M i c δ p)) (δ (μρ-fst M i c δ p)) p₁ , 
                     δ₁ (μρ M i c δ (μρ-fst M i c δ p) p₁))
                    (ε₁ (μρ M i c δ (μρ-fst M i c δ p) p₁))))
      → (e : q' == graft-slc-ρ-from (τ M i c (μρ-fst M i c δ p))
                     (δ (μρ-fst M i c δ p)) (ε (μρ-fst M i c δ p))
                     (λ q₁ → δ₁ (μρ M i c δ (μρ-fst M i c δ p) q₁))
                     (λ q₁ → ε₁ (μρ M i c δ (μρ-fst M i c δ p) q₁))
                       (graft-slc-ρ-to (τ M i c (μρ-fst M i c δ p))
                         (δ (μρ-fst M i c δ p)) (ε (μρ-fst M i c δ p))
                         (λ q₁ → δ₁ (μρ M i c δ (μρ-fst M i c δ p) q₁))
                         (λ q₁ → ε₁ (μρ M i c δ (μρ-fst M i c δ p) q₁))
                           (inr (μρ-snd M i c δ p ,
                                transport! (λ pn → ρ-slc (τ M i (μ M i c δ) (fst pn) , δ₁ (fst pn)) (snd pn))
                                           (pair= (μρ-η M i c δ p) (apd ε₁ (μρ-η M i c δ p))) q))))
      → graft-slc-ρ-from-lcl i c δ ε δ₁ ε₁ (μρ-fst M i c δ p) q' == inr (p , q)

    graft-slc-ρ-from-to i .(η M i) (dot .i) δ₁ ε₁ (inl ())
    graft-slc-ρ-from-to i .(η M i) (dot .i) δ₁ ε₁ (inr (p , q)) =
      let ρ-slc-ε₁ q = ρ-slc (τ M i (η M i) q , δ₁ q) (ε₁ q)
      in ap inr (pair= (ηρ-η M i p) (to-transp-↓ ρ-slc-ε₁ (ηρ-η M i p) q ))
    graft-slc-ρ-from-to i .(μ M i c δ) (box .i c δ ε) δ₁ ε₁ (inl (inl unit)) = idp
    graft-slc-ρ-from-to i .(μ M i c δ) (box .i c δ ε) δ₁ ε₁ (inl (inr (p , q))) = 
      let  δ₁' p q = δ₁ (μρ M i c δ p q)
           ε₁' p q = ε₁ (μρ M i c δ p q)
           δ' p = μ M (τ M i c p) (δ p) (δ₁' p)
           gs-from = graft-slc-ρ-from (τ M i c p) (δ p) (ε p) (δ₁' p) (ε₁' p)
           gs-to = graft-slc-ρ-to (τ M i c p) (δ p) (ε p) (δ₁' p) (ε₁' p) 
      in graft-slc-ρ-from-to-lcl₀ i c δ ε δ₁ ε₁ p q (gs-from (gs-to (inl q))) idp 
    graft-slc-ρ-from-to i .(μ M i c δ) (box .i c δ ε) δ₁ ε₁ (inr (p , q)) = 
      let p₀ = μρ-fst M i c δ p
          p₁ = μρ-snd M i c δ p
          δ₁' q = δ₁ (μρ M i c δ p₀ q)
          ε₁' q = ε₁ (μρ M i c δ p₀ q)
          coh = μρ-η M i c δ p 
          ρ-slc-snd pn = ρ-slc (τ M i (μ M i c δ) (fst pn) , δ₁ (fst pn)) (snd pn)
          gs-from = graft-slc-ρ-from (τ M i c p₀) (δ p₀) (ε p₀) δ₁' ε₁'
          gs-to = graft-slc-ρ-to (τ M i c p₀) (δ p₀) (ε p₀) δ₁' ε₁'
          el = inr (p₁ , transport! ρ-slc-snd (pair= coh (apd ε₁ coh)) q)
      in graft-slc-ρ-from-to-lcl₁ i c δ ε δ₁ ε₁ p q (gs-from (gs-to el)) idp

    graft-slc-ρ-from-to-lcl₀ i c δ ε δ₁ ε₁ p q (inl q₀) e = 
      let  δ₁' p q = δ₁ (μρ M i c δ p q)
           ε₁' p q = ε₁ (μρ M i c δ p q)
           δ' p = μ M (τ M i c p) (δ p) (δ₁' p)
           gs-from = graft-slc-ρ-from (τ M i c p) (δ p) (ε p) (δ₁' p) (ε₁' p)
           gs-to = graft-slc-ρ-to (τ M i c p) (δ p) (ε p) (δ₁' p) (ε₁' p)
           ih = graft-slc-ρ-from-to (τ M i c p) (δ p) (ε p) (δ₁' p) (ε₁' p) (inl q) 
           lem = inl q₀                   =⟨ e ⟩
                 gs-from (gs-to (inl q))  =⟨ ih ⟩ 
                 inl q ∎
      in ap (λ x → inl (inr (p , x))) (fst (inl=inl-equiv q₀ q) lem)
    graft-slc-ρ-from-to-lcl₀ i c δ ε δ₁ ε₁ p q (inr (p₀ , q₀)) e = 
      let  δ₁' p q = δ₁ (μρ M i c δ p q)
           ε₁' p q = ε₁ (μρ M i c δ p q)
           δ' p = μ M (τ M i c p) (δ p) (δ₁' p)
           gs-from = graft-slc-ρ-from (τ M i c p) (δ p) (ε p) (δ₁' p) (ε₁' p)
           gs-to = graft-slc-ρ-to (τ M i c p) (δ p) (ε p) (δ₁' p) (ε₁' p)
           ih = graft-slc-ρ-from-to (τ M i c p) (δ p) (ε p) (δ₁' p) (ε₁' p) (inl q)
           lem = inr (p₀ , q₀)            =⟨ e ⟩
                 gs-from (gs-to (inl q))  =⟨ ih ⟩ 
                 inl q ∎
      in ⊥-elim (inr≠inl (p₀ , q₀) q lem)

    graft-slc-ρ-from-to-lcl₁ i c δ ε δ₁ ε₁ p q (inl q₀) e = 
      let p₀ = μρ-fst M i c δ p
          p₁ = μρ-snd M i c δ p
          δ₁' q = δ₁ (μρ M i c δ p₀ q)
          ε₁' q = ε₁ (μρ M i c δ p₀ q)
          coh = μρ-η M i c δ p 
          ρ-slc-snd pn = ρ-slc (τ M i (μ M i c δ) (fst pn) , δ₁ (fst pn)) (snd pn)
          gs-from = graft-slc-ρ-from (τ M i c p₀) (δ p₀) (ε p₀) δ₁' ε₁'
          gs-to = graft-slc-ρ-to (τ M i c p₀) (δ p₀) (ε p₀) δ₁' ε₁'
          el = (p₁ , transport! ρ-slc-snd (pair= coh (apd ε₁ coh)) q)
          ih = graft-slc-ρ-from-to (τ M i c p₀) (δ p₀) (ε p₀) δ₁' ε₁' (inr el)
          lem = inl q₀ =⟨ e ⟩ 
                gs-from (gs-to (inr el)) =⟨ ih ⟩ 
                inr el ∎
      in ⊥-elim (inl≠inr q₀ el lem)
    graft-slc-ρ-from-to-lcl₁ i c δ ε δ₁ ε₁ p q (inr (p₀ , q₀)) e =
      let r₀ = μρ-fst M i c δ p
          r₁ = μρ-snd M i c δ p
          δ₁' q = δ₁ (μρ M i c δ r₀ q)
          ε₁' q = ε₁ (μρ M i c δ r₀ q)
          coh = μρ-η M i c δ p 
          ρ-slc-ε₁ q₁ = ρ-slc (τ M i (μ M i c δ) q₁ , δ₁ q₁) (ε₁ q₁)
          ρ-slc-snd pn = ρ-slc (τ M i (μ M i c δ) (fst pn) , δ₁ (fst pn)) (snd pn)
          gs-from = graft-slc-ρ-from (τ M i c r₀) (δ r₀) (ε r₀) δ₁' ε₁'
          gs-to = graft-slc-ρ-to (τ M i c r₀) (δ r₀) (ε r₀) δ₁' ε₁'
          el = (r₁ , transport! ρ-slc-snd (pair= coh (apd ε₁ coh)) q)
          ih = graft-slc-ρ-from-to (τ M i c r₀) (δ r₀) (ε r₀) δ₁' ε₁' (inr el)
          lem₀ = inr (p₀ , q₀) =⟨ e ⟩
                 gs-from (gs-to (inr el)) =⟨ ih ⟩ 
                 inr el ∎
          lem₁ = to-transp-↓ ρ-slc-snd (pair= coh (apd ε₁ coh)) q
          lem₂ = ↓-apd-lem (curry ρ-slc-snd) ε₁ coh lem₁
          lem₃ = fst (inr=inr-equiv (p₀ , q₀) el) lem₀
          lem = μρ M i c δ r₀ p₀ , q₀
                  =⟨ pair= (ap (μρ M i c δ r₀) (fst= lem₃)) (↓-ap-in ρ-slc-ε₁ (μρ M i c δ r₀) (snd= lem₃)) ⟩
                μρ M i c δ r₀ r₁ , snd el
                  =⟨ pair= (μρ-η M i c δ p) lem₂ ⟩ 
                p , q ∎
      in ap inr lem

    graft-slc-ρ-equiv : (i : I) (c : γ M i) (n : Nst i c)
      → (δ₁ : (p : ρ M i c) → γ M (τ M i c p))
      → (ε₁ : (p : ρ M i c) → Nst (τ M i c p) (δ₁ p)) 
      → ρ-slc (i , c) n ⊔ Σ (ρ M i c) (λ p → ρ-slc (τ M i c p , δ₁ p) (ε₁ p))
        ≃' ρ-slc (i , μ M i c δ₁) (graft-slc i c n δ₁ ε₁)
    graft-slc-ρ-equiv i c n δ₁ ε₁ = 
      equiv' (graft-slc-ρ-to i c n δ₁ ε₁) (graft-slc-ρ-from i c n δ₁ ε₁)
             (graft-slc-ρ-to-from i c n δ₁ ε₁) (graft-slc-ρ-from-to i c n δ₁ ε₁)
    
    --
    --  Joining, and the equivalence of places
    --

    μ-slc : (i : I-slc) (n : γ-slc i) (κ : (p : ρ-slc i n) → γ-slc (τ-slc i n p)) → γ-slc i
    μ-slc (i , .(η M i)) (dot .i) κ = dot i
    μ-slc (i , .(μ M i c δ)) (box .i c δ ε) κ =
      let κ' p q = κ (inr (p , q))
          ε' p = μ-slc (τ M i c p , δ p) (ε p) (κ' p)
      in graft-slc i c (κ (inl unit)) δ ε'

    μρ-slc-to : (i : I-slc) (n : γ-slc i)
      → (κ : (p : ρ-slc i n) → γ-slc (τ-slc i n p))
      → Σ (ρ-slc i n) (λ q → ρ-slc (τ-slc i n q) (κ q))
      → ρ-slc i (μ-slc i n κ)
    μρ-slc-to (i , .(η _ i)) (dot .i) κ (() , q₁)
    μρ-slc-to (i , .(μ _ i c δ)) (box .i c δ ε) κ (inl unit , q₁) =
      let κ' p q = κ (inr (p , q))
          ε' p = μ-slc (τ M i c p , δ p) (ε p) (κ' p)
      in graft-slc-ρ-to i c (κ (inl unit)) δ ε' (inl q₁)
    μρ-slc-to (i , .(μ _ i c δ)) (box .i c δ ε) κ (inr (p₀ , q₀) , q₁) = 
      let κ' p q = κ (inr (p , q))
          ε' p = μ-slc (τ M i c p , δ p) (ε p) (κ' p)
      in graft-slc-ρ-to i c (κ (inl unit)) δ ε'
           (inr (p₀ , (μρ-slc-to (τ M i c p₀ , δ p₀) (ε p₀) (κ' p₀) (q₀ , q₁)))) 
      
    μρ-slc-from : (i : I-slc) (n : γ-slc i)
      → (κ : (p : ρ-slc i n) → γ-slc (τ-slc i n p))
      → ρ-slc i (μ-slc i n κ)
      → Σ (ρ-slc i n) (λ q → ρ-slc (τ-slc i n q) (κ q))

    μρ-slc-from-lcl : (i : I) (c : γ M i)
      → (δ : (p : ρ M i c) → γ M (τ M i c p))
      → (ε : (p : ρ M i c) → Nst (τ M i c p) (δ p))
      → (κ : (p : ⊤ ⊔ (Σ (ρ M i c) (λ p₁ →
          ρ-slc (τ M i c p₁ , δ p₁) (ε p₁)))) → γ-slc (τ-slc (i , μ M i c δ) (box i c δ ε) p))
      → ρ-slc (i , c) (κ (inl unit)) ⊔ Σ (ρ M i c) (λ p →
          ρ-slc (τ M i c p , δ p) (μ-slc (τ M i c p , δ p) (ε p) (λ q₁ → κ (inr (p , q₁)))))
      → Σ (⊤ ⊔ (Σ (ρ M i c) (λ p → ρ-slc (τ M i c p , δ p) (ε p))))
          (λ q → ρ-slc (τ-slc (i , μ M i c δ) (box i c δ ε) q) (κ q))

    μρ-slc-from (i , .(η _ i)) (dot .i) κ ()
    μρ-slc-from (i , .(μ _ i c δ)) (box .i c δ ε) κ q = 
      let κ' p q = κ (inr (p , q))
          ε' p = μ-slc (τ M i c p , δ p) (ε p) (κ' p)
      in μρ-slc-from-lcl i c δ ε κ (graft-slc-ρ-from i c (κ (inl unit)) δ ε' q)

    μρ-slc-from-lcl i c δ ε κ (inl q₀) = inl unit , q₀
    μρ-slc-from-lcl i c δ ε κ (inr (p₀ , q₀)) =
      let κ' q = κ (inr (p₀ , q))
          ih = μρ-slc-from (τ M i c p₀ , δ p₀) (ε p₀) κ' q₀
      in inr (p₀ , fst ih) , snd ih

    μρ-slc-to-from : (i : I-slc) (n : γ-slc i)
      → (κ : (p : ρ-slc i n) → γ-slc (τ-slc i n p))
      → (q : ρ-slc i (μ-slc i n κ))
      → μρ-slc-to i n κ (μρ-slc-from i n κ q) == q

    μρ-slc-to-from-lcl : (i : I) (c : γ M i)
      → (δ : (p : ρ M i c) → γ M (τ M i c p))
      → (ε : (p : ρ M i c) → Nst (τ M i c p) (δ p))
      → (κ : (p : ⊤ ⊔ (Σ (ρ M i c) (λ p₁ → ρ-slc (τ M i c p₁ , δ p₁) (ε p₁)))) 
             → γ-slc (τ-slc (i , μ M i c δ) (box i c δ ε) p))
      → (q : ρ-slc (i , μ M i c δ) (graft-slc i c (κ (inl unit)) δ
               (λ p → μ-slc (τ M i c p , δ p) (ε p) (λ q₁ → κ (inr (p , q₁))))))
      → (q' : ρ-slc (i , c) (κ (inl unit)) ⊔ Σ (ρ M i c)
                (λ p → ρ-slc (τ M i c p , δ p)
                         (μ-slc (τ M i c p , δ p) (ε p) (λ q₁ → κ (inr (p , q₁))))))
      → (e : q' == (graft-slc-ρ-from i c (κ (inl unit)) δ
                    (λ p → μ-slc (τ M i c p , δ p) (ε p) (λ q₁ → κ (inr (p , q₁)))) q))
      → μρ-slc-to (i , μ M i c δ) (box i c δ ε) κ
          (μρ-slc-from-lcl i c δ ε κ q') == q

    μρ-slc-to-from (i , .(η _ i)) (dot .i) κ ()
    μρ-slc-to-from (i , .(μ _ i c δ)) (box .i c δ ε) κ q = 
      let κ' p q = κ (inr (p , q))
          ε' p = μ-slc (τ M i c p , δ p) (ε p) (κ' p)
      in μρ-slc-to-from-lcl i c δ ε κ q (graft-slc-ρ-from i c (κ (inl unit)) δ ε' q) idp

    μρ-slc-to-from-lcl i c δ ε κ q (inl q₀) e =
      let n' = κ (inl unit)
          κ' p q = κ (inr (p , q))
          ε' p = μ-slc (τ M i c p , δ p) (ε p) (κ' p)
          gs-to = graft-slc-ρ-to i c n' δ ε'
          gs-from = graft-slc-ρ-from i c n' δ ε'
          ih = graft-slc-ρ-to-from i c n' δ ε' q
          lem = gs-to (inl q₀) =⟨ ap gs-to e ⟩
                gs-to (gs-from q) =⟨ ih ⟩ 
                q ∎
      in lem
    μρ-slc-to-from-lcl i c δ ε κ q (inr (p₀ , q₀)) e = 
      let n' = κ (inl unit)
          κ' p q = κ (inr (p , q))
          i' p = (τ M i c p , δ p)
          ε' p = μ-slc (i' p) (ε p) (κ' p)
          gs-to = graft-slc-ρ-to i c n' δ ε'
          gs-from = graft-slc-ρ-from i c n' δ ε'
          ih = graft-slc-ρ-to-from i c n' δ ε' q
          mst = μρ-slc-to (i' p₀) (ε p₀) (κ' p₀)
          msf = μρ-slc-from (i' p₀) (ε p₀) (κ' p₀)
          lem = gs-to (inr (p₀ , mst (msf q₀)))
                  =⟨ μρ-slc-to-from (i' p₀) (ε p₀) (κ' p₀) q₀ |in-ctx (λ x → gs-to (inr (p₀ , x))) ⟩
                gs-to (inr (p₀ , q₀))
                  =⟨ ap gs-to e ⟩
                gs-to (gs-from q) =⟨ ih ⟩
                q ∎
      in lem

    μρ-slc-from-to : (i : I-slc) (n : γ-slc i)
      → (κ : (p : ρ-slc i n) → γ-slc (τ-slc i n p))
      → (q : Σ (ρ-slc i n) (λ q₀ → ρ-slc (τ-slc i n q₀) (κ q₀)))
      → μρ-slc-from i n κ (μρ-slc-to i n κ q) == q

    μρ-slc-from-to-lcl : (i : I) (c : γ M i)
      → (δ : (p : ρ M i c) → γ M (τ M i c p))
      → (ε : (p : ρ M i c) → Nst (τ M i c p) (δ p))
      → (κ : (p : ⊤ ⊔ (Σ (ρ M i c) (λ p₁ → ρ-slc (τ M i c p₁ , δ p₁) (ε p₁)))) 
             → γ-slc (τ-slc (i , μ M i c δ) (box i c δ ε) p))
      → (q : Σ (⊤ ⊔ (Σ (ρ M i c) (λ p → ρ-slc (τ M i c p , δ p) (ε p))))
                  (λ q₀ → ρ-slc (τ-slc (i , μ M i c δ) (box i c δ ε) q₀) (κ q₀)))
      → (q' : ρ-slc (i , c) (κ (inl unit)) ⊔ Σ (ρ M i c)
                (λ p → ρ-slc (τ M i c p , δ p)
                  (μ-slc (τ M i c p , δ p) (ε p) (λ q₁ → κ (inr (p , q₁))))))
      → (e : q' == graft-slc-ρ-from i c (κ (inl unit)) δ
                    (λ p → μ-slc (τ M i c p , δ p) (ε p) (λ q₁ → κ (inr (p , q₁))))
                    (μρ-slc-to (i , μ M i c δ) (box i c δ ε) κ q))
      → μρ-slc-from-lcl i c δ ε κ q' == q

    μρ-slc-from-to (i , .(η _ i)) (dot .i) κ (() , _)
    μρ-slc-from-to (i , .(μ _ i c δ)) (box .i c δ ε) κ q = 
      let κ' p q = κ (inr (p , q))
          ε' p = μ-slc (τ M i c p , δ p) (ε p) (κ' p)
      in μρ-slc-from-to-lcl i c δ ε κ q
           (graft-slc-ρ-from i c (κ (inl unit)) δ ε'
             (μρ-slc-to (i , μ M i c δ) (box i c δ ε) κ q)) idp

    μρ-slc-from-to-lcl i c δ ε κ (inl unit , q₀) (inl q₁) e =
      let n' = κ (inl unit)
          κ' p q = κ (inr (p , q))
          ε' p = μ-slc (τ M i c p , δ p) (ε p) (κ' p)
          gs-to = graft-slc-ρ-to i c n' δ ε'
          gs-from = graft-slc-ρ-from i c n' δ ε'
          ih = graft-slc-ρ-from-to i c n' δ ε' (inl q₀)
          lem = inl q₁ =⟨ e ⟩
                gs-from (gs-to (inl q₀)) =⟨ ih ⟩ 
                inl q₀ ∎
      in ap (λ z → inl unit , z) (fst (inl=inl-equiv q₁ q₀) lem)

    μρ-slc-from-to-lcl i c δ ε κ (inl unit , q₀) (inr q₁) e = 
      let n' = κ (inl unit)
          κ' p q = κ (inr (p , q))
          ε' p = μ-slc (τ M i c p , δ p) (ε p) (κ' p)
          gs-to = graft-slc-ρ-to i c n' δ ε'
          gs-from = graft-slc-ρ-from i c n' δ ε'
          ih = graft-slc-ρ-from-to i c n' δ ε' (inl q₀)
          lem = inr q₁ =⟨ e ⟩
                gs-from (gs-to (inl q₀)) =⟨ ih ⟩ 
                inl q₀ ∎
      in ⊥-elim (inr≠inl q₁ q₀ lem)

    μρ-slc-from-to-lcl i c δ ε κ (inr (p , q) , q₀) (inl q₁) e = 
      let n' = κ (inl unit)
          κ' p q = κ (inr (p , q))
          ε' p = μ-slc (τ M i c p , δ p) (ε p) (κ' p)
          p₀ = μρ-slc-to (τ M i c p , δ p) (ε p) (κ' p) (q , q₀)
          gs-to = graft-slc-ρ-to i c n' δ ε'
          gs-from = graft-slc-ρ-from i c n' δ ε'
          ih = graft-slc-ρ-from-to i c n' δ ε' (inr (p , p₀))
          lem = inl q₁ =⟨ e ⟩
                gs-from (gs-to (inr (p , p₀))) =⟨ ih ⟩ 
                inr (p , p₀) ∎
      in ⊥-elim (inl≠inr q₁ (p , p₀) lem)

    μρ-slc-from-to-lcl i c δ ε κ (inr (p , q) , q₀) (inr (p₁ , q₁)) e = 
      let n' = κ (inl unit)
          κ' p q = κ (inr (p , q))
          ε' p = μ-slc (τ M i c p , δ p) (ε p) (κ' p)
          p₀ = μρ-slc-to (τ M i c p , δ p) (ε p) (κ' p) (q , q₀)
          gs-to = graft-slc-ρ-to i c n' δ ε'
          gs-from = graft-slc-ρ-from i c n' δ ε'
          ih = graft-slc-ρ-from-to i c n' δ ε' (inr (p , p₀))
          msf p = μρ-slc-from (τ M i c p , δ p) (ε p) (κ' p)
          msft = μρ-slc-from-to (τ M i c p , δ p) (ε p) (κ' p) (q , q₀)
          lem₀ = inr (p₁ , q₁) =⟨ e ⟩
                 gs-from (gs-to (inr (p , p₀))) =⟨ ih ⟩
                 inr (p , p₀) ∎
          lem₁ = fst (inr=inr-equiv (p₁ , q₁) (p , p₀)) lem₀
          lem₃ = (apd↓-cst (λ {p₁} → msf p₁) (snd= lem₁)) ∙'ᵈ msft
      in pair= (ap inr (pair= (fst= lem₁) (↓-Σ-fst lem₃)))
               (↓-ap-in (λ x → ρ-slc (τ-slc (i , μ M i c δ) (box i c δ ε) x) (κ x)) inr (↓-Σ-snd lem₃))

    μρ-equiv-slc : (i : I-slc) (n : γ-slc i)
      → (κ : (p : ρ-slc i n) → γ-slc (τ-slc i n p))
      → Σ (ρ-slc i n) (λ q → ρ-slc (τ-slc i n q) (κ q))
        ≃' ρ-slc i (μ-slc i n κ)
    μρ-equiv-slc i n κ =
      equiv' (μρ-slc-to i n κ) (μρ-slc-from i n κ)
             (μρ-slc-to-from i n κ) (μρ-slc-from-to i n κ)

  data Mnd where
    id : (I : Type₀) → Mnd I
    fr : {I : Type₀} (P : Poly I) → Mnd I
    slc : {I : Type₀} (M : Mnd I) → Mnd (Σ I (γ M))
    pb : {I : Type₀} (M : Mnd I) (X : I → Type₀) → Mnd (Σ I X)

  --
  --  Decoding functions
  --
  
  γ (id I) i = ⊤
  γ (fr P) = γ-fr P
  γ (slc M) = γ-slc M
  γ (pb M X) = γ-pb M X

  ρ (id I) i unit = ⊤
  ρ (fr P) = ρ-fr P
  ρ (slc M) = ρ-slc M
  ρ (pb M X) = ρ-pb M X 

  τ (id I) i unit unit = i
  τ (fr P) = τ-fr P
  τ (slc M) = τ-slc M
  τ (pb M X) = τ-pb M X 

  η (id I) _ = unit
  η (fr P) = η-fr P
  η (slc M) = η-slc M
  η (pb M X) = η-pb M X

  μ (id I) i unit δ = unit
  μ (fr P) = μ-fr P
  μ (slc M) = μ-slc M
  μ (pb M X) = μ-pb M X 

  ηρ-contr (id I) _ = Unit-level
  ηρ-contr (fr P) = ηρ-contr-fr P
  ηρ-contr (slc M) = ηρ-contr-slc M
  ηρ-contr (pb M X) = ηρ-contr-pb M X

  μρ-equiv (id I) i unit δ =
    equiv' (λ { (unit , unit) → unit }) (λ { unit → unit , unit })
           (λ { unit → idp }) (λ { (unit , unit) → idp })
  μρ-equiv (fr P) = μρ-equiv-fr P
  μρ-equiv (slc M) = μρ-equiv-slc M 
  μρ-equiv (pb M X) = μρ-equiv-pb M X
