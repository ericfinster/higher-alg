{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Poly

module InftyOperad where

  Frame : {I : Type₀} (P : Poly I) {i : I} (w : W P i) (c : γ P i) → Type₀
  Frame {I} P w c = (j : I) → Leaf P w j ≃ ρ P c j

  _//_ : {I : Type₀} (P : Poly I) (F : {i : I} {w : W P i} {c : γ P i} → Frame P w c → Type₀) → Poly (Σ I (γ P))
  γ (P // F) (i , c) = Σ (W P i) (λ w → Σ (Frame P w c) F)
  ρ (P // F) (w , f , x) (j , d) = Node P w d

  -- record PSet {I : Type₀} (P : Poly I) : Type₁ where
  --   coinductive
  --   field

  --     Filler : {i : I} {w : W P i} {c : γ P i} → frame P w c → Type₀
  --     Higher : PSet (FillPoly P Filler)

  -- open PSet public
  
  -- record is-algebraic {I : Type₀} {P : Poly I} (X : PSet P) : Type₁ where
  --   coinductive
  --   field

  --     has-fillers : {i : I} (w : W P i)
  --       → is-contr (Σ (γ P i) (λ c → Σ (frame P w c) (Filler X)))

  --     higher-has-fillers : is-algebraic (Higher X)

  -- open is-algebraic public

  -- -- A better idea would be to name this module so that you
  -- -- can instantiate the various basic operations for varying
  -- -- PSets as you go ...
  -- module _ {I : Type₀} {P : Poly I} (O : PSet P) (is-alg : is-algebraic O) where

  --   μ : {i : I} (w : W P i) → γ P i
  --   μ w = fst (contr-center (has-fillers is-alg w))

  --   μρ-eqv : {i : I} (w : W P i) (j : I) → Leaf P w j ≃ ρ P (μ w) j
  --   μρ-eqv w = fst (snd (contr-center (has-fillers is-alg w)))
    
  --   μ-witness : {i : I} (w : W P i) → Filler O (μρ-eqv w)
  --   μ-witness w = snd (snd (contr-center (has-fillers is-alg w))) 

  --   η : (i : I) → γ P i
  --   η i = μ (lf i)

  --   ηρ-eqv : (i : I) (j : I) → Leaf P (lf i) j ≃ ρ P (η i) j
  --   ηρ-eqv i = μρ-eqv (lf i)
    
  --   ηρ-contr : (i : I) → is-contr (Σ I (ρ P (η i)))
  --   ηρ-contr i = equiv-preserves-level (Σ-emap-r (ηρ-eqv i)) ⦃ lf-lf-contr P i ⦄


  -- --   unary-op : (i : I) → Type₀
  -- --   unary-op i = Σ (γ P i) (λ c → is-contr (ρ P i c))

  -- --   u-domain : {i : I} (u : unary-op i) → I
  -- --   u-domain {i} (c , e) = τ P i c (contr-center e)

  -- --   urinv : (i : I) (u : unary-op i) → Type₀
  -- --   urinv i (u , is-c) = Σ (γ P (τ P i u (contr-center is-c))) (λ v → μ (nd i (u , (λ p → transport (W P) (ap (τ P i u) (contr-path is-c p)) (corolla P v)))) == η i)

  -- --   pre-comp-map : (i : I) (u : unary-op i)
  -- --     → γ P (u-domain u) → γ P i
  -- --   pre-comp-map i (u , is-c) c = μ (nd i (u , λ p → transport (W P) (ap (τ P i u) (contr-path is-c p)) (corolla P c)))

  -- --   -- So what if we say that u is invertible if this map is an equivalence?
  -- --   -- I guess it's at least obviously a proposition....

  -- --   η-op : (i : I) → unary-op i
  -- --   η-op i = η i , has-level-in (–> (μ-plc-eqv (lf i)) tt , <–-inv-r (μ-plc-eqv (lf i)))

  -- --   Arrow : I → I → Type₀
  -- --   Arrow i j = Σ (unary-op j) (λ u → u-domain u == i)

  -- --   id-arrow : (i : I) → Arrow i i
  -- --   id-arrow i = η-op i , ! (μ-plc-coh (lf i) tt)

  -- --   -- the last guy wants us to prove that the type of this guy
  -- --   -- is i, where that's the domain of f.
  -- --   Comp : (i j k : I) → Arrow i j → Arrow j k → Arrow i k
  -- --   Comp i j k ((f , α) , idp) ((g , β) , idp) = (μ w , is-c) , coh 

  -- --     where w : W P k
  -- --           w = nd k (g , λ p → transport (W P) ((ap (τ P k g) (contr-path β p))) (corolla P f))
            
  -- --           lf-eqv : (p : ρ P k g) → leaf P (corolla P f) ≃ leaf P (transport (W P) (ap (τ P k g) (contr-path β p)) (corolla P f))
  -- --           lf-eqv p = leaf-inv P (corolla P f) (ap (τ P k g) (contr-path β p))

  -- --           is-c : is-contr (ρ P k (μ w))
  -- --           is-c = equiv-preserves-level (μ-plc-eqv w)
  -- --                    ⦃ Σ-level β (λ p → equiv-preserves-level
  -- --                      (leaf-inv P (corolla P f) (ap (τ P k g) (contr-path β p))
  -- --                        ∘e (corolla-ρ-eqv P f)⁻¹ ) ⦃ α ⦄) ⦄

  -- --           l = –> (lf-eqv (contr-center β)) ((contr-center α) , tt)
            
  -- --           coh = τ P k (μ w) (contr-center is-c)
  -- --                   =⟨ (contr-path is-c) (–> (μ-plc-eqv w) (contr-center β , l)) |in-ctx (λ x → τ P k (μ w) x) ⟩
  -- --                 τ P k (μ w) (–> (μ-plc-eqv w) (contr-center β , l))
  -- --                   =⟨ ! (μ-plc-coh w (contr-center β , l)) ⟩
  -- --                 leaf-type P (transport (W P) (ap (τ P k g) (contr-path β (contr-center β))) (corolla P f)) l
  -- --                   =⟨ ! (leaf-inv-coh P (corolla P f) (ap (τ P k g) (contr-path β (contr-center β))) ((contr-center α) , tt)) ⟩
  -- --                 τ P (τ P k g (contr-center β)) f (contr-center α) ∎

  -- --   l-inv : {i : I} (u : unary-op i) → Type₀
  -- --   l-inv {i} u = Σ (Arrow i j) (λ l → fst (fst (Comp j i j (u , idp) l)) == η j)

  -- --     where j = u-domain u

  -- --   r-inv : {i : I} (u : unary-op i) → Type₀
  -- --   r-inv {i} u = Σ (Arrow i j) (λ r → fst (fst (Comp i j i r (u , idp))) == η i)

  -- --     where j = u-domain u

  -- --   is-invertible : ∀ {i} (u : unary-op i) → Type₀
  -- --   is-invertible u = l-inv u × r-inv u

  -- module _ {I : Type₀} {P : Poly I} (O : PSet P) (is-alg : is-algebraic O) where

  -- --   -- The proof here is that μ is a homomorphism, automatically.
  -- --   -- But I wonder if it's not better to give an elementary proof here...
  -- --   unit-l : (i : I) (w : W P i)
  -- --     → μ O is-alg (nd i (η O is-alg i , λ p → transport! (W P) (ηρ-typ O is-alg i p) w)) == μ O is-alg w
  -- --   unit-l i w = {!!}

  -- --   -- Better or worse?
  -- --   unit-l' : (i : I) (δ : (p : ρ P i (η O is-alg i)) → W P (τ P i (η O is-alg i) p))
  -- --     → μ O is-alg (δ (contr-center (ηρ-contr O is-alg i))) == μ O is-alg (nd i (η O is-alg i , δ))
  -- --       [ γ P ↓ ηρ-typ O is-alg i (contr-center (ηρ-contr O is-alg i)) ]
  -- --   unit-l' i δ = {!!}

  --   -- This one is amusing, you use the unit in the next dimension!
  --   unit-r : (i : I) (c : γ P i)
  --     → μ O is-alg (corolla P c) == c
  --   unit-r i c = ap (μ O is-alg) claim₂ ∙ claim₁
  
  --     where ηic = η (Higher O) (higher-has-fillers is-alg) (i , c) 

  --           corolla' : W P i
  --           corolla' = fst ηic

  --           have : (j : Σ I (γ P)) → Leaf (FillPoly P (Filler O)) (lf (i , c)) j ≃ Node P corolla' (snd j)
  --           have = ηρ-eqv (Higher O) (higher-has-fillers is-alg) (i , c)

  --           know : is-contr (Σ (Σ I (γ P)) (ρ (FillPoly P (Filler O)) ηic)) 
  --           know = ηρ-contr (Higher O) (higher-has-fillers is-alg) (i , c)

  --           know' : is-contr (Σ (Σ I (γ P)) (Node P corolla' ∘ snd))
  --           know' = ηρ-contr (Higher O) (higher-has-fillers is-alg) (i , c)

  --           -- ρ (FillPoly F) (w , f , x) (j , d) = Node P w d

  --           claim₁ : μ O is-alg corolla' == c
  --           claim₁ = fst= (contr-path (has-fillers is-alg corolla') (c , snd ηic))

  --           -- Bingo.  And now just a lemma about the corolla being unique with
  --           -- these properties and you're done!
  --           claim₂ : corolla P c == corolla'
  --           claim₂ = {!have (i , c)!}

