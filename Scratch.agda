--
--  Temporary storage while I finish the slice monad
--

  --
  --  Decoding functions
  --
  
  -- γ (id I) i = ⊤
  -- γ (slc M) = γ-slc M
  -- -- γ (pb M X) = γ-pb M X

  -- ρ (id I) unit = ⊤
  -- ρ (slc M) = ρ-slc M
  -- -- ρ (pb M X) {i = i} = ρ-pb M X {i = i}

  -- τ (id I) {i} unit = i
  -- τ (slc M) = τ-slc M
  -- -- τ (pb M X) {i = i} {c = c} = τ-pb M X {i = i} {c = c}

  -- η (id I) _ = unit
  -- η (slc M) = η-slc M
  -- -- η (pb M X) = η-pb M X

  -- μ (id I) unit _ = unit
  -- μ (slc M) = μ-slc M
  -- -- μ (pb M X) {i = i} = μ-pb M X {i = i}

  -- ηp (id I) _ = unit
  -- ηp (slc M) = ηp-slc M
  -- -- ηp (pb M X) = ηp-pb M X

  -- μρ (id I) _ _ _ = unit
  -- μρ (slc M) = μρ-slc M
  -- -- μρ (pb M X) {i = i} {c = c} = μρ-pb M X {i = i} {c = c}

  -- ηp-η (id I) i unit = idp
  -- ηp-η (slc M) = ηp-η-slc M
  -- -- ηp-η (pb M X) = ηp-η-pb M X

  -- μρ-fst (id I) _ _ = unit
  -- μρ-fst (slc M) = μρ-fst-slc M
  -- -- μρ-fst (pb M X) {i = i} {c = c} = μρ-fst-pb M X {i = i} {c = c}
  
  -- μρ-snd (id I) _ _ = unit
  -- μρ-snd (slc M) = μρ-snd-slc M
  -- -- μρ-snd (pb M X) {i = i} {c = c} = μρ-snd-pb M X {i = i} {c = c}
  

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
