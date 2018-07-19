{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Inspect

module Poly where

  record Poly (I : Type₀) : Type₁ where
    field
      γ : I → Type₀
      ρ : {i : I} (c : γ i) (j : I) → Type₀

  open Poly public

  ⟦_⟧ : {I : Type₀} (P : Poly I) → (I → Set) → I → Set
  ⟦ P ⟧ X i = Σ (γ P i) (λ c → ∀ j → (p : ρ P c j) → X j)

  module _ {I : Type₀} (P : Poly I) where
  
    data W : I → Type₀ where
      lf : (i : I) → W i
      nd : {i : I} → ⟦ P ⟧ W i → W i

    ↓-nd-in : {i j : I} (c₀ : γ P i) (c₁ : γ P j)
      → (δ₀ : ∀ k → (p : ρ P c₀ k) → W k) 
      → (δ₁ : ∀ k → (p : ρ P c₁ k) → W k) 
      → (q : i == j) (r : c₀ == c₁ [ γ P ↓ q ])
      → (s : ∀ k l → (s : k == l) (p₀ : ρ P c₀ k) (p₁ : ρ P c₁ l)
                    → δ₀ k p₀ == δ₁ l p₁ [ W ↓ s ])
      → nd (c₀ , δ₀) == nd (c₁ , δ₁) [ W ↓ q ]
    ↓-nd-in c₀ c₁ δ₀ δ₁ idp idp s =
      ap (λ x → nd (c₀ , x)) (λ= (λ j → λ= (λ p → s j j idp p p)))

    ↓-nd-in' : {i j : I} (c₀ : γ P i) (c₁ : γ P j)
      → (δ₀ : ∀ k → (p : ρ P c₀ k) → W k) 
      → (δ₁ : ∀ k → (p : ρ P c₁ k) → W k) 
      → (q : i == j) (r : c₀ == c₁ [ γ P ↓ q ])
      → (s : ∀ k → (p₀ : ρ P c₀ k) (p₁ : ρ P c₁ k) → δ₀ k p₀ == δ₁ k p₁)
      → nd (c₀ , δ₀) == nd (c₁ , δ₁) [ W ↓ q ]
    ↓-nd-in' c₀ c₁ δ₀ δ₁ idp idp s =
      ap (λ x → nd (c₀ , x)) (λ= (λ j → λ= (λ p → s j p p)))

    -- ↓-nd-in' : {i j : I} (c₀ : γ P i) (c₁ : γ P j)
    --   → (δ₀ : ∀ k → (p : ρ P c₀ k) → W k) 
    --   → (δ₁ : ∀ k → (p : ρ P c₁ k) → W k) 
    --   → (q : i == j) (r : c₀ == c₁ [ γ P ↓ q ])
    --   → (s : ∀ k l → (p₀ : ρ P c₀ k) (p₁ : ρ P c₁ l)
    --                → (k , δ₀ k p₀) == (l , δ₁ l p₁))
    --   → nd (c₀ , δ₀) == nd (c₁ , δ₁) [ W ↓ q ]
    -- ↓-nd-in' c₀ c₁ δ₀ δ₁ q r s = {!!}
      -- ap (λ x → nd (c₀ , x)) (λ= (λ j → λ= (λ p → {!ev j j p p!})))

    data Leaf : {i : I} (w : W i) → I → Type₀ where
      leaf : (i : I) → Leaf (lf i) i
      stem : {i : I} (c : γ P i)
        → (δ : ∀ j → (p : ρ P c j) → W j)
        → {j : I} → (p : ρ P c j)
        → {k : I} → Leaf (δ j p) k
        → Leaf (nd (c , δ)) k

    lf-lf-contr : (i : I) → is-contr (Σ I (Leaf (lf i)))
    lf-lf-contr i = has-level-in ((i , leaf i) , λ { (_ , leaf .i) → idp })

    data Node : {i : I} (w : W i) {j : I} (c : γ P j) → Type₀ where
      this : {i : I} (c : γ P i)
        → (δ : ∀ j → (p : ρ P c j) → W j)
        → Node (nd (c , δ)) c
      that : {i : I} (c : γ P i)
        → (δ : ∀ j → (p : ρ P c j) → W j)
        → {j : I} → (p : ρ P c j)
        → {k : I} → {d : γ P k} → Node (δ j p) d
        → Node (nd (c , δ)) d

    -- Used in Baez-Dolan substitution
    nd-lf-eqv : {i : I} (c : γ P i)
      → (δ : ∀ j → (p : ρ P c j) → W j) (k : I)
      → Σ I (λ j → Σ (ρ P c j) (λ p → Leaf (δ j p) k))
        ≃ Leaf (nd (c , δ)) k
    nd-lf-eqv c δ k = equiv to from to-from from-to

      where PlcLf = Σ I (λ j → Σ (ρ P c j) (λ p → Leaf (δ j p) k))

            to : PlcLf → Leaf (nd (c , δ)) k
            to (i , p , l) = stem c δ p l

            from : Leaf (nd (c , δ)) k → PlcLf
            from (stem c δ p l) = _ , p , l

            to-from : ∀ l → to (from l) == l
            to-from (stem c δ p l) = idp

            from-to : ∀ pl → from (to pl) == pl
            from-to (i , p , l) = idp

    corolla : {i : I} (c : γ P i) → W i
    corolla {i} c = nd (c , λ j p → lf j)

    corolla-lf-eqv : {i : I} (c : γ P i)
      → (j : I) → Leaf (corolla c) j ≃ ρ P c j
    corolla-lf-eqv c j = equiv to from (λ _ → idp) from-to

      where to : Leaf (corolla c) j → ρ P c j
            to (stem c _ p (leaf i)) = p

            from : ρ P c j → Leaf (corolla c) j
            from p = stem c _ p (leaf j)

            from-to : (l : Leaf (corolla c) j) → from (to l) == l
            from-to (stem c _ p (leaf i)) = idp

    _≋_ : {i : I} (w₀ w₁ : W i) → Type₀
    w₀ ≋ w₁ = {i : I} (c : γ P i) → Node w₀ c ≃ Node w₁ c 

    lf-eqv : {i j : I} (w₀ : W i) (w₁ : W j) → Type₀
    lf-eqv w₀ w₁ = (k : I) → Leaf w₀ k ≃ Leaf w₁ k

    nd-eqv : {i j : I} (w₀ : W i) (w₁ : W j) → Type₀
    nd-eqv w₀ w₁ = {k : I} (c : γ P k) → Node w₀ c ≃ Node w₁ c

    node-height : {i j : I} {w : W i} {c : γ P j} → Node w c → ℕ
    node-height {w = lf i} ()
    node-height {w = nd (c , δ)} (this .c .δ) = O
    node-height {w = nd (c , δ)} (that .c .δ p n) = S (node-height n)

    is-height-preserving' : {i j : I} {w₀ : W i} {w₁ : W j} → nd-eqv w₀ w₁ → Type₀
    is-height-preserving' {_} {_} {w₀} {w₁} e =
      (k : I) (c : γ P k) (n : Node w₀ c)
      → node-height n == node-height (–> (e c) n)

    is-height-preserving : {i : I} {w₀ w₁ : W i} → w₀ ≋ w₁ → Type₀
    is-height-preserving {_} {w₀} {w₁} e =
      (i : I) (c : γ P i) (n : Node w₀ c)
      → node-height n == node-height (–> (e c) n)

    is-height-preserving-is-prop : {i : I} {w₀ w₁ : W i} (e : w₀ ≋ w₁)
      → is-prop (is-height-preserving e)
    is-height-preserving-is-prop e =
      Π-level (λ i → Π-level (λ c → Π-level (λ n →
        has-level-apply ℕ-is-set (node-height n) (node-height (–> (e c) n)))))

    lf-nd-elim : ∀ {ℓ} {X : Type ℓ} {i j : I} {c : γ P j} → Node (lf i) c → X
    lf-nd-elim ()

    -- module Local {i j : I} (c₀ : γ P i) (c₁ : γ P j)
    --   (δ₀ : ∀ j → ρ P c₀ j → W j)
    --   (δ₁ : ∀ j → ρ P c₁ j → W j)
    --   (e : nd-eqv (nd (c₀ , δ₀)) (nd (c₁ , δ₁)))
    --   (is-hp : is-height-preserving' e) where

    -- base-path' : {i j : I} (c₀ : γ P i) (c₁ : γ P j) (α : i == j)
    --   → (δ₀ : ∀ j → ρ P c₀ j → W j)
    --   → (δ₁ : ∀ j → ρ P c₁ j → W j)
    --   → (e : nd-eqv (nd (c₀ , δ₀)) (nd (c₁ , δ₁)))
    --   → (is-hp : is-height-preserving' e)
    --   → (i , c₀) == (j , c₁)
    -- base-path' c₀ c₁ α δ₀ δ₁ e is-hp with (–> (e c₀) (this c₀ δ₀)) | inspect (–> (e c₀)) (this c₀ δ₀)
    -- base-path' c₀ .c₀ α δ₀ δ₁ e is-hp | this .c₀ .δ₁ | _ = {!!}
    -- base-path' c₀ c₁ α δ₀ δ₁ e is-hp | that .c₁ .δ₁ p n | ingraph x =
    --   ⊥-elim (ℕ-O≠S (node-height n) (is-hp _ c₀ (this c₀ δ₀) ∙ ap node-height x))

    -- base-path : {i j : I} (c₀ : γ P i) (c₁ : γ P j)
    --   → (δ₀ : ∀ j → ρ P c₀ j → W j)
    --   → (δ₁ : ∀ j → ρ P c₁ j → W j)
    --   → (e : nd-eqv (nd (c₀ , δ₀)) (nd (c₁ , δ₁)))
    --   → (is-hp : is-height-preserving' e)
    --   → (i , c₀) == (j , c₁)
    -- base-path c₀ c₁ δ₀ δ₁ e is-hp with (–> (e c₀) (this c₀ δ₀)) | inspect (–> (e c₀)) (this c₀ δ₀)
    -- base-path c₀ .c₀ δ₀ δ₁ e is-hp | this .c₀ .δ₁ | _ = idp
    -- base-path c₀ c₁ δ₀ δ₁ e is-hp | that .c₁ .δ₁ p n | ingraph α =
    --   ⊥-elim (ℕ-O≠S (node-height n) (is-hp _ c₀ (this c₀ δ₀) ∙ ap node-height α))

    -- reconstruct : {i j : I} (w₀ : W i) (w₁ : W j)
    --   → (α : lf-eqv w₀ w₁)
    --   → (β : nd-eqv w₀ w₁)
    --   → (is-hp : is-height-preserving' β)
    --   → (q : i == j) → w₀ == w₁ [ W ↓ q ]
    -- reconstruct (lf i) (lf j) α β is-hp q = apd lf q
    -- reconstruct (lf i) (nd (c₁ , δ₁)) α β is-hp q = lf-nd-elim (<– (β c₁) (this c₁ δ₁))
    -- reconstruct (nd (c₀ , δ₀)) (lf j) α β is-hp q = lf-nd-elim (–> (β c₀) (this c₀ δ₀))
    -- reconstruct (nd (c₀ , δ₀)) (nd (c₁ , δ₁)) α β is-hp q =
    --   ↓-nd-in c₀ c₁ δ₀ δ₁ q {!!}
    --     (λ k l s p₀ p₁ → reconstruct (δ₀ k p₀) (δ₁ l p₁) {!!} {!!} {!!} s)

    -- reconstruct : {i j : I} (w₀ : W i) (w₁ : W j)
    --   → (α : lf-eqv w₀ w₁)
    --   → (β : nd-eqv w₀ w₁)
    --   → (is-hp : is-height-preserving' β)
    --   → (i , w₀) == (j , w₁)
    -- reconstruct (lf i) (lf j) α β is-hp with –> (α i) (leaf i)
    -- reconstruct (lf .j) (lf j) α β is-hp | leaf .j = idp
    -- reconstruct (lf i) (nd (c₁ , δ₁)) α β is-hp = lf-nd-elim (<– (β c₁) (this c₁ δ₁))
    -- reconstruct (nd (c₀ , δ₀)) (lf j) α β is-hp = lf-nd-elim (–> (β c₀) (this c₀ δ₀))
    -- reconstruct (nd (c₀ , δ₀)) (nd (c₁ , δ₁)) α β is-hp with (–> (β c₀) (this c₀ δ₀)) | inspect (–> (β c₀)) (this c₀ δ₀)
    -- reconstruct (nd (c₀ , δ₀)) (nd (c₁ , δ₁)) α β is-hp | that .c₁ .δ₁ p n | x = {!!}
    -- reconstruct (nd {i} (c₀ , δ₀)) (nd (.c₀ , δ₁)) α β is-hp | this .c₀ .δ₁ | ingraph e =
    --   ap (λ x → (i , nd (c₀ , x))) (λ= (λ j → λ= (λ p → {!reconstruct (δ₀ j p) (δ₁ j p) ? ? ?!})))

      -- let bp = base-path c₀ c₁ δ₀ δ₁ β is-hp
      --     ih k l p₀ p₁ = reconstruct (δ₀ k p₀) (δ₁ l p₁) {!!} {!!} {!!}
      -- in pair= (fst= bp) {!!} -- pair= (fst= bp) (↓-nd-in c₀ c₁ δ₀ δ₁ (fst= bp) (snd= bp) {!ih!})
      

    -- Phhhh.  Okay, getting there.  I have to prove the reconstruction lemma.
    -- I feel like this is going to be slightly annoying, which is why I am
    -- hesitating just a bit.

  --   corolla-unique : {i : I} (c : γ P i) (w : W i)
  --     → (is-c : is-contr (node w))
  --     → (pth : node-type w (contr-center is-c) == (i , c))
  --     → corolla c == w 
  --   corolla-unique c (lf i) is-c pth = ⊥-elim (contr-center is-c)
  --   corolla-unique c (nd i (c' , δ)) is-c pth = ap corolla {!!} ∙ and-so

  --     where lem : (i , c') == (i , c)
  --           lem = (! (ap (λ x → node-type (nd i (c' , δ)) x) (contr-path is-c (inl unit)))) ∙ pth

  --           must-be-leaves : (p : ρ P i c') → δ p == lf (τ P i c' p)
  --           must-be-leaves p with δ p | inspect δ p
  --           must-be-leaves p | lf .(τ P i c' p) | ingraph e = idp
  --           must-be-leaves p | nd .(τ P i c' p) _ | ingraph e = ⊥-elim
  --             (inl≠inr unit no-no (contr-has-all-paths ⦃ is-c ⦄ (inl unit) (inr no-no))) 

  --             where no-no : Σ (ρ P i c') (node ∘ δ)
  --                   no-no = p , transport! node e (inl unit)

  --           and-so : corolla c' == nd i (c' , δ)
  --           and-so = ap (λ d → nd i (c' , d)) (λ= (λ p → ! (must-be-leaves p)))

  module _ {I : Type₀} (P : Poly I) where

    Fr : Poly I
    γ Fr = W P
    ρ Fr w = Leaf P w

    graft : {i : I} (w : W P i) (ε : ∀ j → Leaf P w j → W P j) → W P i
    graft (lf i) ε = ε i (leaf i)
    graft (nd (c , δ)) ε =
      let ε' j p k l = ε k (stem c δ p l)
          δ' j p = graft (δ j p) (ε' j p)
      in nd (c , δ')

    --
    --  Leaves in a graft
    --

    graft-leaf-to : {i : I} (w : W P i) (ε : ∀ j → Leaf P w j → W P j) (k : I)
      → Leaf P (graft w ε) k
      → Σ I (λ j → Σ (Leaf P w j) (λ l → Leaf P (ε j l) k))
    graft-leaf-to (lf i) ε k l = i , leaf i , l
    graft-leaf-to (nd (c , δ)) ε k (stem _ _ {j} p l) = 
      let (s , t , u) = graft-leaf-to (δ j p) (λ k l → ε k (stem c δ p l)) k l
      in s , stem _ _ p t , u

    graft-leaf-from : {i : I} (w : W P i) (ε : ∀ j → Leaf P w j → W P j) (k : I)
      → Σ I (λ j → Σ (Leaf P w j) (λ l → Leaf P (ε j l) k))
      → Leaf P (graft w ε) k
    graft-leaf-from (lf i) ε k (.i , leaf .i , l) = l
    graft-leaf-from (nd (c , δ)) ε k (j , stem _ _ p l₀ , l₁) = 
      let ε' j p k l = ε k (stem c δ p l)
          δ' j p = graft (δ j p) (ε' j p)
      in stem c _ p (graft-leaf-from (δ _ p) (ε' _ p) k (j , l₀ , l₁))

    graft-leaf-to-from : {i : I} (w : W P i) (ε : ∀ j → Leaf P w j → W P j) (k : I)
      → (l : Σ I (λ j → Σ (Leaf P w j) (λ l → Leaf P (ε j l) k)))
      → graft-leaf-to w ε k (graft-leaf-from w ε k l) == l
    graft-leaf-to-from (lf i) ε k (.i , leaf .i , l₁) = idp
    graft-leaf-to-from (nd (c , δ)) ε k (j , stem _ _ p l₀ , l₁) =
      let ε' j p k l = ε k (stem c δ p l)
          δ' j p = graft (δ j p) (ε' j p)
          (s , t , u) = graft-leaf-to (δ _ p) (ε' _ p) k
                          (graft-leaf-from (δ _ p) (ε' _ p) k (j , l₀ , l₁))
          ih = graft-leaf-to-from (δ _ p) (ε' _ p) k (j , l₀ , l₁)
      in pair= (fst= ih) (apd↓-cst (λ x → (stem c δ p (fst x) , snd x)) (snd= ih)) 

    graft-leaf-from-to : {i : I} (w : W P i) (ε : ∀ j → Leaf P w j → W P j)
      → (k : I) (l : Leaf P (graft w ε) k)
      → graft-leaf-from w ε k (graft-leaf-to w ε k l) == l
    graft-leaf-from-to (lf i) ε k l = idp
    graft-leaf-from-to (nd (c , δ)) ε k (stem _ _ {j} p l) =
      let ε' j p k l = ε k (stem c δ p l)
          δ' j p = graft (δ j p) (ε' j p)
      in ap (λ x → stem c δ' p x) (graft-leaf-from-to (δ j p) (ε' j p) k l) 

    graft-leaf-eqv : {i : I} (w : W P i) (ε : ∀ j → Leaf P w j → W P j) (k : I)
      → Leaf P (graft w ε) k
        ≃ Σ I (λ j → Σ (Leaf P w j) (λ l → Leaf P (ε j l) k))
    graft-leaf-eqv w ε k =
      equiv (graft-leaf-to w ε k) (graft-leaf-from w ε k)
            (graft-leaf-to-from w ε k) (graft-leaf-from-to w ε k)

    -- --
    -- --  Nodes in a graft
    -- --
    
    -- graft-nd-to : (i : I) (w : W P i)
    --   → (ε : (l : leaf P w) → W P (leaf-type P w l))
    --   → node P w ⊔ Σ (leaf P w) (node P ∘ ε) 
    --   → node P (graft i w ε)
    -- graft-nd-to i (lf .i) ε (inl ())
    -- graft-nd-to i (lf .i) ε (inr (unit , n)) = n
    -- graft-nd-to i (nd .i (c , δ)) ε (inl true) = inl unit
    -- graft-nd-to i (nd .i (c , δ)) ε (inl (inr (p , n))) =
    --   inr (p , graft-nd-to (τ P i c p) (δ p) (λ l → ε (p , l)) (inl n))
    -- graft-nd-to i (nd .i (c , δ)) ε (inr ((p , l) , n)) =
    --   inr (p , (graft-nd-to (τ P i c p) (δ p) (λ l → ε (p , l)) (inr (l , n))))
    
    -- graft-nd-from : (i : I) (w : W P i)
    --   → (ε : (l : leaf P w) → W P (leaf-type P w l))
    --   → node P (graft i w ε)
    --   → node P w ⊔ Σ (leaf P w) (node P ∘ ε) 
    -- graft-nd-from i (lf .i) ε n = inr (tt , n)
    -- graft-nd-from i (nd .i (c , δ)) ε (inl unit) = inl (inl unit)
    -- graft-nd-from i (nd .i (c , δ)) ε (inr (p , n)) with graft-nd-from (τ P i c p) (δ p) (λ l → ε (p , l)) n
    -- graft-nd-from i (nd .i (c , δ)) ε (inr (p , n)) | inl n' = inl (inr (p , n'))
    -- graft-nd-from i (nd .i (c , δ)) ε (inr (p , n)) | inr (l , n') = inr ((p , l) , n')

    -- graft-nd-to-from : (i : I) (w : W P i)
    --   → (ε : (l : leaf P w) → W P (leaf-type P w l))
    --   → (n : node P (graft i w ε))
    --   → graft-nd-to i w ε (graft-nd-from i w ε n) == n
    -- graft-nd-to-from i (lf .i) ε n = idp
    -- graft-nd-to-from i (nd .i (c , δ)) ε (inl unit) = idp
    -- graft-nd-to-from i (nd .i (c , δ)) ε (inr (p , n)) with
    --   (graft-nd-from (τ P i c p) (δ p) (λ l → ε (p , l))) n |
    --   inspect (graft-nd-from (τ P i c p) (δ p) (λ l → ε (p , l))) n
    -- graft-nd-to-from i (nd .i (c , δ)) ε (inr (p , n)) | inl n' | ingraph e =
    --   ap (λ x → inr (p , x)) lem
  
    --   where lem = graft-nd-to (τ P i c p) (δ p) (λ l → ε (p , l)) (inl n')
    --                 =⟨ ! e |in-ctx (λ x → graft-nd-to (τ P i c p) (δ p) (λ l → ε (p , l)) x) ⟩
    --               graft-nd-to (τ P i c p) (δ p) (λ l → ε (p , l))
    --                 (graft-nd-from (τ P i c p) (δ p) (λ l → ε (p , l)) n)
    --                 =⟨ graft-nd-to-from (τ P i c p) (δ p) (λ l → ε (p , l)) n ⟩ 
    --               n ∎ 

    -- graft-nd-to-from i (nd .i (c , δ)) ε (inr (p , n)) | inr (l , n') | ingraph e = 
    --   ap (λ x → inr (p , x)) lem

    --   where lem = graft-nd-to (τ P i c p) (δ p) (λ l₁ → ε (p , l₁)) (inr (l , n'))
    --                 =⟨ ! e |in-ctx (λ x → graft-nd-to (τ P i c p) (δ p) (λ l₁ → ε (p , l₁)) x) ⟩ 
    --               graft-nd-to (τ P i c p) (δ p) (λ l₁ → ε (p , l₁))
    --                 (graft-nd-from (τ P i c p) (δ p) (λ l₁ → ε (p , l₁)) n)
    --                 =⟨ graft-nd-to-from (τ P i c p) (δ p) (λ l → ε (p , l)) n ⟩ 
    --               n ∎

    -- graft-nd-from-to : (i : I) (w : W P i)
    --   → (ε : (l : leaf P w) → W P (leaf-type P w l))
    --   → (n : node P w ⊔ Σ (leaf P w) (node P ∘ ε))
    --   → graft-nd-from i w ε (graft-nd-to i w ε n) == n
    -- graft-nd-from-to i (lf .i) ε (inl ())
    -- graft-nd-from-to i (lf .i) ε (inr (unit , n)) = idp
    -- graft-nd-from-to i (nd .i (c , δ)) ε (inl (inl unit)) = idp
    -- graft-nd-from-to i (nd .i (c , δ)) ε (inl (inr (p , n))) with 
    --   (graft-nd-from (τ P i c p) (δ p) (λ l → ε (p , l)) ∘ graft-nd-to (τ P i c p) (δ p) (λ l → ε (p , l))) (inl n)
    --   | inspect (graft-nd-from (τ P i c p) (δ p) (λ l → ε (p , l)) ∘ graft-nd-to (τ P i c p) (δ p) (λ l → ε (p , l))) (inl n)
    -- graft-nd-from-to i (nd .i (c , δ)) ε (inl (inr (p , n))) | inl n' | ingraph e =
    --   ap (λ x → inl (inr (p , x))) (–> (inl=inl-equiv n' n) lem)

    --   where lem = inl n' =⟨ ! e ⟩
    --               graft-nd-from (τ P i c p) (δ p) (λ l → ε (p , l))
    --                 (graft-nd-to (τ P i c p) (δ p) (λ l → ε (p , l)) (inl n))
    --                 =⟨ graft-nd-from-to (τ P i c p) (δ p) (λ l → ε (p , l)) (inl n) ⟩ 
    --               inl n ∎
                  
    -- graft-nd-from-to i (nd .i (c , δ)) ε (inl (inr (p , n))) | inr (l , n') | ingraph e =
    --   ⊥-elim ((inr≠inl (l , n') n) lem)

    --   where lem = inr (l , n') =⟨ ! e ⟩ 
    --               graft-nd-from (τ P i c p) (δ p) (λ l₁ → ε (p , l₁))
    --                 (graft-nd-to (τ P i c p) (δ p) (λ l₁ → ε (p , l₁)) (inl n))
    --                 =⟨ graft-nd-from-to (τ P i c p) (δ p) (λ l → ε (p , l)) (inl n) ⟩ 
    --               inl n ∎

    -- graft-nd-from-to i (nd .i (c , δ)) ε (inr ((p , l) , n)) with
    --   (graft-nd-from (τ P i c p) (δ p) (λ l → ε (p , l)) ∘ graft-nd-to (τ P i c p) (δ p) (λ l → ε (p , l))) (inr (l , n))
    --   | inspect (graft-nd-from (τ P i c p) (δ p) (λ l → ε (p , l)) ∘ graft-nd-to (τ P i c p) (δ p) (λ l → ε (p , l))) (inr (l , n))
    -- graft-nd-from-to i (nd .i (c , δ)) ε (inr ((p , l) , n)) | inl n' | ingraph e =
    --   ⊥-elim (inl≠inr n' (l , n) lem)

    --   where lem = inl n' =⟨ ! e ⟩
    --               graft-nd-from (τ P i c p) (δ p) (λ l₁ → ε (p , l₁))
    --                 (graft-nd-to (τ P i c p) (δ p) (λ l₁ → ε (p , l₁)) (inr (l , n)))
    --                 =⟨ graft-nd-from-to (τ P i c p) (δ p) (λ l → ε (p , l)) (inr (l , n)) ⟩ 
    --               inr (l , n) ∎ 

    -- graft-nd-from-to i (nd .i (c , δ)) ε (inr ((p , l) , n)) | inr (l' , n') | ingraph e =
    --   ap (λ x → inr ((p , fst x) , snd x)) (–> (inr=inr-equiv (l' , n') (l , n)) lem)

    --   where lem = inr (l' , n') =⟨ ! e ⟩
    --               graft-nd-from (τ P i c p) (δ p) (λ l₁ → ε (p , l₁))
    --                 (graft-nd-to (τ P i c p) (δ p) (λ l₁ → ε (p , l₁)) (inr (l , n)))
    --                 =⟨ graft-nd-from-to (τ P i c p) (δ p) (λ l → ε (p , l)) (inr (l , n)) ⟩ 
    --               inr (l , n) ∎ 

    
    -- graft-nd-eqv : (i : I) (w : W P i)
    --   → (ε : (l : leaf P w) → W P (leaf-type P w l))
    --   → node P w ⊔ Σ (leaf P w) (node P ∘ ε) 
    --     ≃ node P (graft i w ε)
    -- graft-nd-eqv i w ε =
    --   equiv (graft-nd-to i w ε) (graft-nd-from i w ε)
    --         (graft-nd-to-from i w ε) (graft-nd-from-to i w ε)


