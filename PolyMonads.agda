{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Poly 
open import Inspect

module PolyMonads where

  -- Okay, here's an idea for a hack:
  -- you add a kind of constructor to
  -- the places and, in the code below,
  -- every time you recursively call with a place,
  -- you wrap in that constructor.  The idea, then

  -- But maybe instead of a function, you want a
  -- *type constructor*.  The idea would be that you
  -- have a trivial type constructor, isomorphic to
  -- ρ itself.  Hmmm.  Let's think about it.

  data Mnd : Type₀ → Type₁

  γ : {I : Type₀} (M : Mnd I) → I → Type₀
  ρ : {I : Type₀} (M : Mnd I) (i : I) → γ M i → Type₀
  τ : {I : Type₀} (M : Mnd I) (i : I) (c : γ M i) → ρ M i c → I

  η : {I : Type₀} (M : Mnd I) (i : I) → γ M i
  μ : {I : Type₀} (M : Mnd I) (i : I) (c : γ M i) (δ : (p : ρ M i c) → γ M (τ M i c p)) → γ M i

  ηρ : {I : Type₀} (M : Mnd I) (i : I) → ρ M i (η M i)
  ηρ-expand : {I : Type₀} (M : Mnd I) (i : I) → ρ M i (η M i) → ρ M i (η M i)
  ηρ-η : {I : Type₀} (M : Mnd I) (i : I) (p : ρ M i (η M i)) → ηρ M i == p

  μρ : {I : Type₀} (M : Mnd I) (i : I) (c : γ M i)
    → (δ : (p : ρ M i c) → γ M (τ M i c p)) 
    → (p₀ : ρ M i c) (p₁ : ρ M (τ M i c p₀) (δ p₀))
    → ρ M i (μ M i c δ)

  μρ-fst : {I : Type₀} (M : Mnd I) (i : I) (c : γ M i)
    → (δ : (p : ρ M i c) → γ M (τ M i c p))
    → ρ M i (μ M i c δ)
    → ρ M i c

  μρ-snd : {I : Type₀} (M : Mnd I) (i : I) (c : γ M i)
    → (δ : (p : ρ M i c) → γ M (τ M i c p)) 
    → (p : ρ M i (μ M i c δ))
    → ρ M (τ M i c (μρ-fst M i c δ p)) (δ (μρ-fst M i c δ p))

  ⟪_⟫ : {I : Type₀} (M : Mnd I) → (I → Type₀) → I → Type₀
  ⟪ M ⟫ X i = Σ (γ M i) (λ c → (p : ρ M i c) → X (τ M i c p))

  module _ {I : Type₀} (M : Mnd I) where
  
    postulate

      ηρ-expand-rw : (i : I) (p : ρ M i (η M i))
        → ηρ-expand M i p ↦ ηρ M i

      {-# REWRITE ηρ-expand-rw #-}

      ηp-τ : (i : I) (p : ρ M i (η M i))
        → τ M i (η M i) p ↦ i

      {-# REWRITE ηp-τ #-}

      μρ-τ : (i : I) (c : γ M i)
        → (δ : (p : ρ M i c) → γ M (τ M i c p))
        → (p : ρ M i (μ M i c δ))
        → τ M i (μ M i c δ) p ↦ τ M (τ M i c (μρ-fst M i c δ p)) (δ (μρ-fst M i c δ p)) (μρ-snd M i c δ p)

      {-# REWRITE μρ-τ #-}

      μρ-fst-β : (i : I) (c : γ M i)
        → (δ : (p : ρ M i c) → γ M (τ M i c p)) 
        → (p₀ : ρ M i c) (p₁ : ρ M (τ M i c p₀) (δ p₀))
        → μρ-fst M i c δ (μρ M i c δ p₀ p₁) ↦ p₀

      {-# REWRITE μρ-fst-β #-}

      μρ-snd-β : (i : I) (c : γ M i)
        → (δ : (p : ρ M i c) → γ M (τ M i c p)) 
        → (p₀ : ρ M i c) (p₁ : ρ M (τ M i c p₀) (δ p₀))
        → μρ-snd M i c δ (μρ M i c δ p₀ p₁) ↦ p₁

      {-# REWRITE μρ-snd-β #-}

      μρ-η : {I : Type₀} (M : Mnd I) (i : I) (c : γ M i)
        → (δ : (p : ρ M i c) → γ M (τ M i c p)) 
        → (p : ρ M i (μ M i c δ))
        → μρ M i c δ (μρ-fst M i c δ p) (μρ-snd M i c δ p) ↦ p

      {-# REWRITE μρ-η #-}
      
      unit-l : (i : I) (c : γ M i) 
        → μ M i c (λ p → η M (τ M i c p)) ↦ c

      {-# REWRITE unit-l #-}

      unit-r : (i : I)
        → (δ : (p : ρ M i (η M i)) → γ M (τ M i (η M i) p)) 
        → μ M i (η M i) δ ↦ δ (ηρ M i)

      {-# REWRITE unit-r #-}

      assoc : (i : I) (c : γ M i)
              (δ : (p : ρ M i c) → γ M (τ M i c p))
              (ε : (q : ρ M i (μ M i c δ)) → γ M (τ M i (μ M i c δ) q)) →
              μ M i (μ M i c δ) ε ↦ μ M i c (λ p → μ M (τ M i c p) (δ p) (λ q → ε (μρ M i c δ p q))) 

      {-# REWRITE assoc #-}

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
    η-pb (i , x) = η M i , λ p → x

    ηρ-pb : (i : I-pb) → ρ-pb i (η-pb i)
    ηρ-pb (i , x) = ηρ M i
    
    ηρ-η-pb : (i : I-pb) (p : ρ-pb i (η-pb i)) → ηρ-pb i == p
    ηρ-η-pb (i , x) p  = ηρ-η M i p

    μ-pb : (i : I-pb) (c : γ-pb i) (ε : (p : ρ-pb i c) → γ-pb (τ-pb i c p)) → γ-pb i
    μ-pb (i , x) (c , δ) ε = 
      let ε' p = snd (ε (μρ-fst M i c (fst ∘ ε) p)) (μρ-snd M i c (fst ∘ ε) p)
      in μ M i c (fst ∘ ε) , ε' 

    μρ-pb : (i : I-pb) (c : γ-pb i)
      → (ε : (p : ρ-pb i c) → γ-pb (τ-pb i c p))
      → (p₀ : ρ-pb i c) (p₁ : ρ-pb (τ-pb i c p₀) (ε p₀))
      → ρ-pb i (μ-pb i c ε)
    μρ-pb (i , x) (c , δ) ε p₀ p₁ = μρ M i c (fst ∘ ε) p₀ p₁

    μρ-fst-pb : (i : I-pb) (c : γ-pb i)
      → (ε : (p : ρ-pb i c) → γ-pb (τ-pb i c p))
      → (p : ρ-pb i (μ-pb i c ε))
      → ρ-pb i c
    μρ-fst-pb (i , x) (c , δ) ε p = μρ-fst M i c (fst ∘ ε) p

    μρ-snd-pb : (i : I-pb) (c : γ-pb i)
      → (ε : (p : ρ-pb i c) → γ-pb (τ-pb i c p))
      → (p : ρ-pb i (μ-pb i c ε))
      → ρ-pb (τ-pb i c (μρ-fst-pb i c ε p)) (ε (μρ-fst-pb i c ε p))
    μρ-snd-pb (i , x) (c , δ) ε p = μρ-snd M i c (fst ∘ ε) p

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

    --
    --  Grafting
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
    graft-slc-ρ-to i .(η _ i) (dot .i) δ₁ ε₁ (inl ())
    graft-slc-ρ-to i .(η _ i) (dot .i) δ₁ ε₁ (inr (p , q)) =
      -- Only transport left!!!  It should compute away though ...
      transport! (λ p₀ → ρ-slc (τ M i (η M i) p₀ , δ₁ p₀) (ε₁ p₀)) (ηρ-η M i p) q
    graft-slc-ρ-to i .(μ _ i c δ) (box .i c δ ε) δ₁ ε₁ (inl (inl unit)) = inl unit
    graft-slc-ρ-to i .(μ _ i c δ) (box .i c δ ε) δ₁ ε₁ (inl (inr (p , q))) = 
      let  δ₁' p q = δ₁ (μρ M i c δ p q)
           ε₁' p q = ε₁ (μρ M i c δ p q)
           δ' p = μ M (τ M i c p) (δ p) (δ₁' p)
      in inr (p , graft-slc-ρ-to (τ M i c p) (δ p) (ε p) (δ₁' p) (ε₁' p) (inl q))
    graft-slc-ρ-to i .(μ _ i c δ) (box .i c δ ε) δ₁ ε₁ (inr (p , q)) = 
      let  δ₁' p q = δ₁ (μρ M i c δ p q)
           ε₁' p q = ε₁ (μρ M i c δ p q)
           δ' p = μ M (τ M i c p) (δ p) (δ₁' p)
           p₀ = μρ-fst M i c δ p
           p₁ = μρ-snd M i c δ p
      in inr (p₀ , graft-slc-ρ-to (τ M i c p₀) (δ p₀) (ε p₀) (δ₁' p₀) (ε₁' p₀) (inr (p₁ , q)))

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
    
    --
    --  Joining
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

  ηρ (id I) i = unit
  ηρ (fr P) i = unit
  ηρ (slc M) = ηρ-slc M
  ηρ (pb M X) = ηρ-pb M X
  
  ηρ-η (id I) i unit = idp
  ηρ-η (fr P) i unit = idp
  ηρ-η (slc M) = ηρ-η-slc M
  ηρ-η (pb M X) = ηρ-η-pb M X

  ηρ-expand (id I) i p = p
  ηρ-expand (fr P) i p = p
  ηρ-expand (slc M) i p = p
  ηρ-expand (pb M X) i p = p

  μρ (id I) i unit δ unit unit = unit
  μρ (fr P) i c δ p₀ p₁ = μρ-to-fr P i c δ (p₀ , p₁)
  μρ (slc M) i n κ q₀ q₁ = μρ-slc-to M i n κ (q₀ , q₁)
  μρ (pb M X) = μρ-pb M X
  
  μρ-fst (id I) i unit δ unit = unit
  μρ-fst (fr P) i c δ p = fst (μρ-from-fr P i c δ p)
  μρ-fst (slc M) i n κ q = fst (μρ-slc-from M i n κ q)
  μρ-fst (pb M X) = μρ-fst-pb M X
  
  μρ-snd (id I) i unit δ unit = unit
  μρ-snd (fr P) i c δ p = snd (μρ-from-fr P i c δ p)
  μρ-snd (slc M) i n κ q = snd (μρ-slc-from M i n κ q)
  μρ-snd (pb M X) = μρ-snd-pb M X

