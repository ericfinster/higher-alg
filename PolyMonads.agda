{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module PolyMonads where

  data Mnd : Type₀ → Type₁

  γ : {I : Type₀} (M : Mnd I) → I → Type₀
  ρ : {I : Type₀} (M : Mnd I) {i : I} → γ M i → Type₀
  τ : {I : Type₀} (M : Mnd I) {i : I} {c : γ M i} → ρ M c → I

  η : {I : Type₀} (M : Mnd I) → (i : I) → γ M i
  μ : {I : Type₀} (M : Mnd I) {i : I} (c : γ M i) (δ : (p : ρ M c) → γ M (τ M p)) → γ M i

  ηp : {I : Type₀} (M : Mnd I) (i : I) → ρ M (η M i)
  μp : {I : Type₀} (M : Mnd I) {i : I} {c : γ M i}
       (δ : (p : ρ M c) → γ M (τ M p)) → 
       Σ (ρ M c) (ρ M ∘ δ) → ρ M (μ M c δ)

  ⟦_⟧ : {I : Type₀} (M : Mnd I) → (I → Set) → I → Set
  ⟦ M ⟧ X i = Σ (γ M i) (λ c → (p : ρ M c) → X (τ M p))

  ηp-unique : {I : Type₀} (M : Mnd I) (i : I) (p : ρ M (η M i)) → ηp M i == p

  μp-equiv : {I : Type₀} (M : Mnd I) {i : I} {c : γ M i}
             (δ : (p : ρ M c) → γ M (τ M p)) →
             is-equiv (μp M δ)

  μρ-fst : {I : Type₀} (M : Mnd I) {i : I} {c : γ M i}
          (δ : (p : ρ M c) → γ M (τ M p)) → ρ M (μ M c δ) → ρ M c
  μρ-fst M δ pp = fst (is-equiv.g (μp-equiv M δ) pp)

  μρ-snd : {I : Type₀} (M : Mnd I) {i : I} {c : γ M i}
           (δ : (p : ρ M c) → γ M (τ M p)) 
           (pp : ρ M (μ M c δ)) → ρ M (δ (μρ-fst M δ pp))
  μρ-snd M δ pp = snd (is-equiv.g (μp-equiv M δ) pp)

  postulate
    ηp-compat : {I : Type₀} {M : Mnd I} (i : I) →
                τ M (ηp M i) ↦ i
    μp-compat : {I : Type₀} {M : Mnd I} (i : I) (c : γ M i)
                (δ : (p : ρ M c) → γ M (τ M p))
                (p : ρ M c) (q : ρ M (δ p)) → ρ M (μ M c δ) →
                τ M (μp M δ (p , q)) ↦ τ M q

    unit-l : {I : Type₀} {M : Mnd I} (i : I) (c : γ M i) →
             μ M c (λ p → η M (τ M p)) ↦ c

    {-# REWRITE ηp-compat #-}
    {-# REWRITE μp-compat #-}
    {-# REWRITE unit-l #-}

    unit-r : {I : Type₀} {M : Mnd I} (i : I) (δ : (p : ρ M (η M i)) → γ M (τ M p)) →
             μ M (η M i) δ ↦ δ (ηp M i)

    {-# REWRITE unit-r #-}
    
    assoc : {I : Type₀} {M : Mnd I} {i : I} {c : γ M i}
            (δ : (p : ρ M c) → γ M (τ M p))
            (ε : (q : ρ M (μ M c δ)) → γ M (τ M q)) →
            μ M (μ M c δ) ε ↦ μ M c (λ p → μ M (δ p) (λ q → ε (μp M δ (p , q)))) 

    {-# REWRITE assoc #-}

  -- This now follows easily because of the rewrite.
  μp-snd-coh : {I : Type₀} (M : Mnd I) {i : I} {c : γ M i}
               (δ : (p : ρ M c) → γ M (τ M p)) 
               (pp : ρ M (μ M c δ)) →
               τ M (μρ-snd M δ pp) == τ M pp
  μp-snd-coh M δ pp = ap (τ M) (is-equiv.f-g (μp-equiv M δ) pp)

  data Mnd where
    id : (I : Type₀) → Mnd I
    slc : {I : Type₀} (M : Mnd I) → Mnd (Σ I (γ M))
    pb : {I : Type₀} (M : Mnd I) (X : I → Type₀) → Mnd (Σ I X)

  -- The pullback monad
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
    η-pb (i , x) = η M i , λ p → transport (λ p₀ → X (τ M p₀)) (ηp-unique M i p) x

    μ-pb : {i : I-pb} (c : γ-pb i) (ε : (p : ρ-pb {i = i} c) → γ-pb (τ-pb {i = i} {c = c} p)) → γ-pb i
    μ-pb {i , x} (c , δ) ε = μ M c (fst ∘ ε) , λ p → transport X (μp-snd-coh M (fst ∘ ε) p) (ε' p)

      where ε' : (p : ρ M (μ M c (fst ∘ ε))) → X (τ M (μρ-snd M (fst ∘ ε) p))
            ε' p = snd (ε (μρ-fst M (fst ∘ ε) p)) (μρ-snd M (fst ∘ ε) p)

    ηp-pb : (i : I-pb) → ρ-pb {i = i} (η-pb i)
    ηp-pb (i , x) = ηp M i

    μp-pb : {i : I-pb} {c : γ-pb i}
            (ε : (p : ρ-pb {i = i} c) → γ-pb (τ-pb {i = i} {c = c} p)) → 
            Σ (ρ-pb {i = i} c) (λ p → ρ-pb {i = τ-pb {i = i} {c = c} p} (ε p)) →  
            ρ-pb {i = i} (μ-pb {i = i} c ε)
    μp-pb {i , x} {c , δ} ε = μp M (fst ∘ ε)

    ηp-unique-pb : (i : I-pb) (p : ρ-pb {i = i} (η-pb i)) → ηp-pb i == p
    ηp-unique-pb (i , x) p = ηp-unique M i p

    μp-equiv-pb : {i : I-pb} {c : γ-pb i}
                  (ε : (p : ρ-pb {i = i} c) → γ-pb (τ-pb {i = i} {c = c} p)) →
                  is-equiv (μp-pb {i = i} {c = c} ε)
    μp-equiv-pb ε = μp-equiv M (fst ∘ ε)                  

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
      δ₁' p q = δ₁ (μp M δ (p , q))

      ε₁' : (p : ρ M c) → (q : ρ M (δ p)) → Nst (δ₁' p q)
      ε₁' p q = ε₁ (μp M δ (p , q))
      
      δ' : (p : ρ M c) → γ M (τ M p)
      δ' p = μ M (δ p) (δ₁' p)

    ηp-slc : (i : I-slc) → ρ-slc (η-slc i)
    ηp-slc (i , c) = inl unit
    
    ηp-unique-slc : (i : I-slc) (p : ρ-slc (η-slc i)) → ηp-slc i == p
    ηp-unique-slc (i , c) (inl unit) = idp
    ηp-unique-slc (i , c) (inr (_ , ()))

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
    slc-graft-ρ-to (dot i) δ₁ ε₁ (inr (p , q)) = transport! (ρ-slc ∘ ε₁) (ηp-unique M i p) q 
    slc-graft-ρ-to (box c δ ε) δ₁ ε₁ (inr (p , q)) = inr (p₀ , IH)
      where open Local δ ε δ₁ ε₁

            p₀ = μρ-fst M δ p
            p₁ = μρ-snd M δ p

            coh : μp M δ (p₀ , p₁) == p
            coh = is-equiv.f-g (μp-equiv M δ) p

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
    slc-graft-ρ-from (box c δ ε) δ₁ ε₁ (inr (p , q)) | inr (p₀ , q₀) = inr (μp M δ (p , p₀) , q₀)

    -- slc-graft-ρ-to-from : {i : I} {c : γ M i} (n : Nst c)
    --                       (δ : (p : ρ M c) → (γ M (τ M p)))
    --                       (ε : (p : ρ M c) → Nst (δ p))
    --                       (q : ρ-slc (slc-graft n δ ε)) →
    --                       slc-graft-ρ-to n δ ε (slc-graft-ρ-from n δ ε q) == q
    -- slc-graft-ρ-to-from (dot i) δ₁ ε₁ q = {!!}
    -- slc-graft-ρ-to-from (box c δ ε) δ₁ ε₁ (inl unit) = idp
    -- slc-graft-ρ-to-from (box c δ ε) δ₁ ε₁ (inr (p , q)) = {!!}

    --   where open Local δ ε δ₁ ε₁

    --         IH : slc-graft-ρ-to (ε p) (δ₁' p) (ε₁' p) (slc-graft-ρ-from (ε p) (δ₁' p) (ε₁' p) q) == q
    --         IH = slc-graft-ρ-to-from (ε p) (δ₁' p) (ε₁' p) q 
            
    -- -- slc-graft-ρ-to-from (box c δ ε) δ₁ ε₁ (inr (p , q)) with let open Local δ ε δ₁ ε₁ in slc-graft-ρ-from (ε p) (δ₁' p) (ε₁' p) q 
    -- -- slc-graft-ρ-to-from (box c δ ε) δ₁ ε₁ (inr (p , q)) | inl q₀ = {!!}
    -- -- slc-graft-ρ-to-from (box c δ ε) δ₁ ε₁ (inr (p , q)) | inr (p₀ , q₀) = {!!}

    -- slc-graft-ρ-from-to : {i : I} {c : γ M i} (n : Nst c)
    --                       (δ : (p : ρ M c) → (γ M (τ M p)))
    --                       (ε : (p : ρ M c) → Nst (δ p))
    --                       (q : ρ-slc n ⊔ Σ (ρ M c) (ρ-slc ∘ ε)) → 
    --                       slc-graft-ρ-from n δ ε (slc-graft-ρ-to n δ ε q) == q
    -- slc-graft-ρ-from-to n δ ε q = {!!}

    --
    --  Joining, and the equivalence of places
    --

    μ-slc : {i : I-slc} (c : γ-slc i) (δ : (p : ρ-slc c) → γ-slc (τ-slc p)) → γ-slc i
    μ-slc (dot i) κ = dot i
    μ-slc (box c δ ε) κ = slc-graft (κ (inl unit)) δ (λ p → μ-slc (ε p) (λ q → κ (inr (p , q))))

    μp-slc : {i : I-slc} {c : γ-slc i}
             (κ : (p : ρ-slc c) → γ-slc (τ-slc p)) →
             Σ (ρ-slc c) (ρ-slc ∘ κ) → ρ-slc (μ-slc c κ)
    μp-slc {c = dot i} κ (() , _)
    μp-slc {c = box c δ ε} κ (inl unit , q) =
      slc-graft-ρ-to (κ (inl unit)) δ (λ p → μ-slc (ε p) (λ q₀ → κ (inr (p , q₀)))) (inl q)
    μp-slc {c = box c δ ε} κ (inr (p , q₀) , q) =
      slc-graft-ρ-to (κ (inl unit)) δ (λ p₁ → μ-slc (ε p₁) (λ q₁ → κ (inr (p₁ , q₁)))) (inr (p , μp-slc (λ q₁ → κ (inr (p , q₁))) (q₀ , q)))


    μρ-slc-inv : {i : I} {c : γ M i} (n : Nst c)
                 (κ : (p : ρ-slc n) → γ-slc (τ-slc p)) → 
                 ρ-slc (μ-slc n κ) → Σ (ρ-slc n) (ρ-slc ∘ κ)
    μρ-slc-inv (dot i) κ ()
    μρ-slc-inv (box c δ ε) κ p with slc-graft-ρ-from (κ (inl unit)) δ (λ p₀ → μ-slc (ε p₀) (λ q → κ (inr (p₀ , q)))) p
    μρ-slc-inv (box c δ ε) κ p | inl p₀ = inl unit , p₀
    μρ-slc-inv (box c δ ε) κ p | inr (p₀ , q) = inr (p₀ , fst IH) , snd IH

      where IH : Σ (ρ-slc (ε p₀)) (λ q₀ → ρ-slc (κ (inr (p₀ , q₀))))
            IH = μρ-slc-inv (ε p₀) (λ q₀ → κ (inr (p₀ , q₀))) q

    -- μp-slc-to-from : {i : I} {c : γ M i} (n : Nst c)
    --                  (κ : (p : ρ-slc n) → γ-slc (τ-slc p)) 
    --                  (p : ρ-slc (μ-slc n κ)) →
    --                  μp-slc κ (μρ-slc-inv n κ p) == p
    -- μp-slc-to-from (dot i) κ ()
    -- μp-slc-to-from (box c δ ε) κ p with slc-graft-ρ-from (κ (inl unit)) δ (λ p₀ → μ-slc (ε p₀) (λ q → κ (inr (p₀ , q)))) p         
    -- μp-slc-to-from (box c δ ε) κ p | inl p₀ = {!!}
    -- μp-slc-to-from (box c δ ε) κ p | inr (p₀ , q) = {!!}

    -- μp-slc-from-to : {i : I} {c : γ M i} (n : Nst c)
    --                  (κ : (p : ρ-slc n) → γ-slc (τ-slc p))
    --                  (pp : Σ (ρ-slc n) (ρ-slc ∘ κ)) →
    --                  μρ-slc-inv n κ (μp-slc κ pp) == pp
    -- μp-slc-from-to (dot i) κ (() , _)
    -- μp-slc-from-to (box c δ ε) κ (inl unit , q) = {!!}
    -- μp-slc-from-to (box c δ ε) κ (inr (p , q₀) , q) = {!!}

    postulate 
      μp-equiv-slc : {i : I-slc} {c : γ-slc i}
                     (κ : (p : ρ-slc c) → γ-slc (τ-slc p)) →
                     is-equiv (μp-slc κ)
                     
    -- μp-equiv-slc {c = c} κ =
    --   is-eq (μp-slc κ) (μρ-slc-inv c κ) {!!} {!!}
    --         -- (μp-slc-to-from c κ)
    --         -- (μp-slc-from-to c κ)                     

  -- Now we finish the decoding functions

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
  η (slc M) = η-slc M
  η (pb M X) = η-pb M X

  μ (id I) unit _ = unit
  μ (slc M) = μ-slc M
  μ (pb M X) {i = i} = μ-pb M X {i = i}

  ηp (id I) _ = unit
  ηp (slc M) = ηp-slc M
  ηp (pb M X) = ηp-pb M X

  μp (id I) _ (_ , _) = unit
  μp (slc M) = μp-slc M
  μp (pb M X) {i = i} {c = c} = μp-pb M X {i = i} {c = c}

  ηp-unique (id I) i unit = idp
  ηp-unique (slc M) = ηp-unique-slc M
  ηp-unique (pb M X) = ηp-unique-pb M X

  μp-equiv (id I) δ =
    is-eq (λ _ → unit)
          (λ _ → unit , unit)
          (λ { unit → idp })
          (λ { (unit , unit) → idp })
  μp-equiv (slc M) = μp-equiv-slc M
  μp-equiv (pb M X) {i = i} {c = c} = μp-equiv-pb M X {i = i} {c = c}
  
