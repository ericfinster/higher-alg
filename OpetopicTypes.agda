{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import StrictPoly

module OpetopicTypes where

  -- Some tests with opetopic types, etc.

  record OpType {ℓ} (M : Mnd ℓ) : Set (lsucc ℓ) where
    coinductive
    field

      Ops : Idx M → Set ℓ
      Rels : OpType (slc (pb M Ops))

  open OpType public
  
  niche : ∀ {ℓ} {M : Mnd ℓ} (X : OpType M) → Idx M → Type ℓ
  niche {M = M} X i = ⟪ M ⟫ (Ops X) i

  filler : ∀ {ℓ} {M : Mnd ℓ} (X : OpType M) {i : Idx M} (n : niche X i) → Type ℓ
  filler X {i = i} n = Σ (Ops X i) (λ x → Ops (Rels X) ((i , x) , n))

  record is-algebraic {ℓ} {M : Mnd ℓ} (X : OpType M) : Type ℓ where
    coinductive
    field

      fillers-contr : {i : Idx M} (n : niche X i) → is-contr (filler X n)
      rels-algebraic : is-algebraic (Rels X)

  open is-algebraic 

  filler-of : ∀ {ℓ} {M : Mnd ℓ} {X : OpType M} {i : Idx M}
              (n : niche X i) (is-alg : is-algebraic X) → Ops X i
  filler-of n is-alg = fst (fst (has-level-apply (fillers-contr is-alg n)))              

  witness-of : ∀ {ℓ} {M : Mnd ℓ} {X : OpType M} {i : Idx M}
               (n : niche X i) (is-alg : is-algebraic X) → Ops (Rels X) ((i , filler-of n is-alg) , n)
  witness-of n is-alg = snd (fst (has-level-apply (fillers-contr is-alg n)))              

  pth-to-id-cell : ∀ {ℓ} {M : Mnd ℓ} (X : OpType M) (is-alg : is-algebraic X)
                   {i : Idx M} (x y : Ops X i) (p : x == y) → 
                   Ops (Rels X) ((i , x) , (η M i , cst y)) 
  pth-to-id-cell {M = M} X is-coh {i} x .x idp = filler-of id-niche (rels-algebraic is-coh)

    where id-niche : niche (Rels X) (((i , x) , (η M i , cst x))) 
          id-niche = dot (i , x) , λ { () }

  record is-complete {ℓ} {M : Mnd ℓ} (X : OpType M) (is-alg : is-algebraic X) : Type ℓ where
    coinductive
    field

      pth-to-id-equiv : {i : Idx M} (x y : Ops X i) → is-equiv (pth-to-id-cell X is-alg x y)
      rels-is-complete : is-complete (Rels X) (rels-algebraic is-alg)

  open is-complete
  
  record ∞Alg {ℓ} (M : Mnd ℓ) : Type (lsucc ℓ) where
    field

      carrier : OpType M
      is-alg : is-algebraic carrier
      is-cmplt : is-complete carrier is-alg

  open ∞Alg public

  --
  --  The terminal algebra
  --
  
  Term : ∀ {ℓ} (M : Mnd ℓ) → OpType M
  Ops (Term M) = cst (Lift ⊤)
  Rels (Term M) = Term (slc (pb M (cst (Lift ⊤))))

  Term-is-algebraic : ∀ {ℓ} (M : Mnd ℓ) → is-algebraic (Term M)
  fillers-contr (Term-is-algebraic M) n = has-level-in ((lift unit , lift unit) , λ { (lift unit , lift unit) → idp })
  rels-algebraic (Term-is-algebraic M) = Term-is-algebraic (slc (pb M (cst (Lift ⊤))))

  Term-is-complete : ∀ {ℓ} (M : Mnd ℓ) → is-complete (Term M) (Term-is-algebraic M)
  pth-to-id-equiv (Term-is-complete {I} M) {i} (lift unit) (lift unit) =
    is-eq (pth-to-id-cell (Term M) (Term-is-algebraic M) {i = i} (lift unit) (lift unit))
    (λ { (lift unit) → idp })
    (λ { (lift unit) → idp })
    (λ { idp → idp })
  rels-is-complete (Term-is-complete M) = Term-is-complete (slc (pb M (cst (Lift ⊤)))) 

  TermAlg : ∀ {ℓ} (M : Mnd ℓ) → ∞Alg M
  carrier (TermAlg M) = Term M
  is-alg (TermAlg M) = Term-is-algebraic M
  is-cmplt (TermAlg M) = Term-is-complete M

  -- --
  -- --  The free algebra
  -- --

  -- PthFib : {I : Type₀} (M : Mnd I) (X : I → Type₀) → Σ (Σ _ (⟪ M ⟫ X)) (γ-pb M (⟪ M ⟫ X)) → Type₀
  -- PthFib M X ((i , (c₀ , δ₀)) , (c , δ)) = let δ' = λ p₀ → fst (δ p₀) in
  --   (c₀ , δ₀) == (μ M i c δ' , λ p → snd (δ (μρ-fst M i c δ' p)) (μρ-snd M i c δ' p))

  -- -- FreeCarrier : {I : Type₀} (M : Mnd I) → (I → Type₀) → OpType M
  -- -- Ops (FreeCarrier M X) = ⟪ M ⟫ X
  -- -- Rels (FreeCarrier M X) = FreeCarrier (slc (pb M (⟪ M ⟫ X))) (PthFib M X)

  -- -- -- Free-is-algebraic : {I : Type₀} (M : Mnd I) (X : I → Type₀) → is-algebraic (FreeCarrier M X)
  -- -- -- fillers-contr (Free-is-algebraic M X) {i} (c , δ) = has-level-in (((c₀ , δ₀) , sc , sδ) , {!!})
  
  -- -- --   where δ' = λ p₀ → fst (δ p₀) 
  -- -- --         c₀ = μ M i c δ'
  -- -- --         δ₀ = λ p → transport X (μρ-snd-coh M i c δ' p) (snd (δ (μρ-fst M i c δ' p)) (μρ-snd M i c δ' p))

  -- -- --         sc : γ-slc (pb M (⟪ M ⟫ X)) ((_ , c₀ , δ₀) , c , δ)
  -- -- --         sc = η-slc (pb M (⟪ M ⟫ X)) ((_ , c₀ , δ₀) , c , δ)

  -- -- --         sδ : (p : ⊤ ⊔ Σ (ρ-pb M (⟪ M ⟫ X) (i , c₀ , δ₀) (c , δ)) (λ p₁ → ⊥)) →
  -- -- --                 PthFib M X (τ-slc (pb M (⟪ M ⟫ X)) ((i , c₀ , δ₀) , c , δ) sc p)
  -- -- --         sδ (inl unit) = idp
  -- -- --         sδ (inr (_ , ()))
          
  -- -- -- rels-algebraic (Free-is-algebraic M X) = {!!}
 
