{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util

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

    data Leaf : {i : I} (w : W i) → I → Type₀ where
      leaf : (i : I) → Leaf (lf i) i
      stem : {i : I} {c : γ P i}
        → {δ : ∀ j → (p : ρ P c j) → W j}
        → {j : I} → (p : ρ P c j)
        → {k : I} → Leaf (δ j p) k
        → Leaf (nd (c , δ)) k

    lf-lf-contr : (i : I) → is-contr (Σ I (Leaf (lf i)))
    lf-lf-contr i = has-level-in ((i , leaf i) , λ { (_ , leaf .i) → idp })

    lf-elim : {i : I} (Q : ∀ j → Leaf (lf i) j → Type₀)
      → (d : Q i (leaf i))
      → (j : I) → (l : Leaf (lf i) j) → Q j l
    lf-elim Q d j (leaf .j) = d
      
    data Node : {i : I} (w : W i) {j : I} (c : γ P j) → Type₀ where
      this : {i : I} {c : γ P i}
        → {δ : ∀ j → (p : ρ P c j) → W j}
        → Node (nd (c , δ)) c
      that : {i : I} {c : γ P i}
        → {δ : ∀ j → (p : ρ P c j) → W j}
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
            to (i , p , l) = stem p l

            from : Leaf (nd (c , δ)) k → PlcLf
            from (stem p l) = _ , p , l

            to-from : ∀ l → to (from l) == l
            to-from (stem p l) = idp

            from-to : ∀ pl → from (to pl) == pl
            from-to (i , p , l) = idp

    corolla : {i : I} (c : γ P i) → W i
    corolla {i} c = nd (c , λ j p → lf j)

    corolla-lf-eqv : {i : I} (c : γ P i)
      → (j : I) → Leaf (corolla c) j ≃ ρ P c j
    corolla-lf-eqv c j = equiv to from (λ _ → idp) from-to

      where to : Leaf (corolla c) j → ρ P c j
            to (stem p (leaf i)) = p

            from : ρ P c j → Leaf (corolla c) j
            from p = stem p (leaf j)

            from-to : (l : Leaf (corolla c) j) → from (to l) == l
            from-to (stem p (leaf i)) = idp

  module _ {I : Type₀} (P : Poly I) where

    Fr : Poly I
    γ Fr = W P
    ρ Fr w = Leaf P w

    graft : {i : I} (w : W P i) (ε : ∀ j → Leaf P w j → W P j) → W P i
    graft (lf i) ε = ε i (leaf i)
    graft (nd (c , δ)) ε =
      let ε' j p k l = ε k (stem p l)
          δ' j p = graft (δ j p) (ε' j p)
      in nd (c , δ')

    --
    --  Leaves in a graft
    --

    graft-leaf-to : {i : I} (w : W P i) (ε : ∀ j → Leaf P w j → W P j) (k : I)
      → Leaf P (graft w ε) k
      → Σ I (λ j → Σ (Leaf P w j) (λ l → Leaf P (ε j l) k))
    graft-leaf-to (lf i) ε k l = i , leaf i , l
    graft-leaf-to (nd (c , δ)) ε k (stem p l) = 
      let (s , t , u) = graft-leaf-to (δ _ p) (λ k l → ε k (stem p l)) k l
      in s , stem p t , u

    graft-leaf-from : {i : I} (w : W P i) (ε : ∀ j → Leaf P w j → W P j) (k : I)
      → Σ I (λ j → Σ (Leaf P w j) (λ l → Leaf P (ε j l) k))
      → Leaf P (graft w ε) k
    graft-leaf-from (lf i) ε k (.i , leaf .i , l) = l
    graft-leaf-from (nd (c , δ)) ε k (j , stem p l₀ , l₁) = 
      let ε' j p k l = ε k (stem p l)
          δ' j p = graft (δ j p) (ε' j p)
      in stem p (graft-leaf-from (δ _ p) (ε' _ p) k (j , l₀ , l₁))

    graft-leaf-to-from : {i : I} (w : W P i) (ε : ∀ j → Leaf P w j → W P j) (k : I)
      → (l : Σ I (λ j → Σ (Leaf P w j) (λ l → Leaf P (ε j l) k)))
      → graft-leaf-to w ε k (graft-leaf-from w ε k l) == l
    graft-leaf-to-from (lf i) ε k (.i , leaf .i , l₁) = idp
    graft-leaf-to-from (nd (c , δ)) ε k (j , stem p l₀ , l₁) =
      let ε' j p k l = ε k (stem p l)
          δ' j p = graft (δ j p) (ε' j p)
          (s , t , u) = graft-leaf-to (δ _ p) (ε' _ p) k
                          (graft-leaf-from (δ _ p) (ε' _ p) k (j , l₀ , l₁))
          ih = graft-leaf-to-from (δ _ p) (ε' _ p) k (j , l₀ , l₁)
      in pair= (fst= ih) (apd↓-cst (λ x → (stem p (fst x) , snd x)) (snd= ih)) 

    graft-leaf-from-to : {i : I} (w : W P i) (ε : ∀ j → Leaf P w j → W P j)
      → (k : I) (l : Leaf P (graft w ε) k)
      → graft-leaf-from w ε k (graft-leaf-to w ε k l) == l
    graft-leaf-from-to (lf i) ε k l = idp
    graft-leaf-from-to (nd (c , δ)) ε k (stem p l) =
      let ε' j p k l = ε k (stem p l)
          δ' j p = graft (δ j p) (ε' j p)
      in ap (λ x → stem p x) (graft-leaf-from-to (δ _ p) (ε' _ p) k l) 

    graft-leaf-eqv : {i : I} (w : W P i) (ε : ∀ j → Leaf P w j → W P j) (k : I)
      → Leaf P (graft w ε) k
        ≃ Σ I (λ j → Σ (Leaf P w j) (λ l → Leaf P (ε j l) k))
    graft-leaf-eqv w ε k =
      equiv (graft-leaf-to w ε k) (graft-leaf-from w ε k)
            (graft-leaf-to-from w ε k) (graft-leaf-from-to w ε k)

    --
    --  Nodes in a graft
    --

    graft-node-to : {i : I} (w : W P i)
      → (ε : ∀ j → Leaf P w j → W P j)
      → {j : I} (c : γ P j)
      → Node P w c ⊔ Σ I (λ k → Σ (Leaf P w k) (λ l → Node P (ε k l) c))
      → Node P (graft w ε) c
    graft-node-to (lf i) ε c₀ (inl ())
    graft-node-to (lf i) ε c₀ (inr (.i , leaf .i , n)) = n
    graft-node-to (nd (c , δ)) ε .c (inl this) = this
    graft-node-to (nd (c , δ)) ε c₀ (inl (that p n)) =
      that p (graft-node-to (δ _ p) (λ k l → ε k (stem p l)) c₀ (inl n))
    graft-node-to (nd (c , δ)) ε c₀ (inr (k , stem p l , n)) = 
      that p (graft-node-to (δ _ p) (λ k l → ε k (stem p l)) c₀ (inr (k , l , n)))

    graft-node-from : {i : I} (w : W P i)
      → (ε : ∀ j → Leaf P w j → W P j)
      → {j : I} (c : γ P j)
      → Node P (graft w ε) c
      → Node P w c ⊔ Σ I (λ k → Σ (Leaf P w k) (λ l → Node P (ε k l) c))
    graft-node-from (lf i) ε c₀ n = inr (i , leaf i , n)
    graft-node-from (nd (c , δ)) ε .c this = inl this
    graft-node-from (nd (c , δ)) ε c₀ (that p n) with graft-node-from (δ _ p) (λ k l → ε k (stem p l)) c₀ n
    graft-node-from (nd (c , δ)) ε c₀ (that p n) | inl n' = inl (that p n')
    graft-node-from (nd (c , δ)) ε c₀ (that p n) | inr (k , l , n') = inr (k , stem p l , n')

    graft-node-to-from : {i : I} (w : W P i)
      → (ε : ∀ j → Leaf P w j → W P j)
      → {j : I} (c : γ P j)
      → (n : Node P (graft w ε) c)
      → graft-node-to w ε c (graft-node-from w ε c n) == n
    graft-node-to-from (lf i) ε c₀ n = idp
    graft-node-to-from (nd (c , δ)) ε .c this = idp
    graft-node-to-from (nd (c , δ)) ε c₀ (that p n) with
      graft-node-from (δ _ p) (λ k l → ε k (stem p l)) c₀ n |
      inspect (graft-node-from (δ _ p) (λ k l → ε k (stem p l)) c₀) n
    graft-node-to-from (nd (c , δ)) ε c₀ (that p n) | inl n' | ingraph e =
      ap (that p) lem

      where lem = graft-node-to (δ _ p) (λ k l → ε k (stem p l)) c₀ (inl n')
                    =⟨ ! e |in-ctx (graft-node-to (δ _ p) (λ k l → ε k (stem p l)) c₀) ⟩
                  graft-node-to (δ _ p) (λ k l → ε k (stem p l)) c₀
                    (graft-node-from (δ _ p) (λ k l → ε k (stem p l)) c₀ n)
                    =⟨ graft-node-to-from (δ _ p) (λ k l → ε k (stem p l)) c₀ n ⟩ 
                  n ∎
                  
    graft-node-to-from (nd (c , δ)) ε c₀ (that p n) | inr (k , l , n') | ingraph e =
      ap (that p) lem

      where lem = graft-node-to (δ _ p) (λ k l → ε k (stem p l)) c₀ (inr (k , l , n')) 
                    =⟨ ! e |in-ctx (graft-node-to (δ _ p) (λ k l → ε k (stem p l)) c₀) ⟩
                  graft-node-to (δ _ p) (λ k l → ε k (stem p l)) c₀
                    (graft-node-from (δ _ p) (λ k l → ε k (stem p l)) c₀ n)
                    =⟨ graft-node-to-from (δ _ p) (λ k l → ε k (stem p l)) c₀ n ⟩ 
                  n ∎


    graft-node-from-to : {i : I} (w : W P i)
      → (ε : ∀ j → Leaf P w j → W P j)
      → {j : I} (c : γ P j)
      → (n : Node P w c ⊔ Σ I (λ k → Σ (Leaf P w k) (λ l → Node P (ε k l) c)))
      → graft-node-from w ε c (graft-node-to w ε c n) == n
    graft-node-from-to (lf i) ε c₀ (inl ())
    graft-node-from-to (lf i) ε c₀ (inr (.i , leaf .i , n)) = idp
    graft-node-from-to (nd (c , δ)) ε .c (inl this) = idp
    graft-node-from-to (nd (c , δ)) ε c₀ (inl (that p n)) with 
      (graft-node-from (δ _ p) (λ k l → ε k (stem p l)) c₀ ∘ graft-node-to (δ _ p) (λ k l → ε k (stem p l)) c₀) (inl n)
      | inspect (graft-node-from (δ _ p) (λ k l → ε k (stem p l)) c₀ ∘ graft-node-to (δ _ p) (λ k l → ε k (stem p l)) c₀) (inl n)
    graft-node-from-to (nd (c , δ)) ε c₀ (inl (that p n)) | inl n' | ingraph e =
      ap (λ x → inl (that p x)) (–> (inl=inl-equiv n' n) lem)

      where lem = inl n' =⟨ ! e ⟩
                  graft-node-from (δ _ p) (λ k l → ε k (stem p l)) c₀
                    (graft-node-to (δ _ p) (λ k l → ε k (stem p l)) c₀ (inl n))
                    =⟨ graft-node-from-to (δ _ p) (λ k l → ε k (stem p l)) c₀ (inl n) ⟩ 
                  inl n ∎

    graft-node-from-to (nd (c , δ)) ε c₀ (inl (that p n)) | inr (k , l , n') | ingraph e =
      ⊥-elim (inr≠inl (k , l , n') n lem)

      where lem = inr (k , l , n') =⟨ ! e ⟩
                  graft-node-from (δ _ p) (λ k₁ l₁ → ε k₁ (stem p l₁)) c₀
                    (graft-node-to (δ _ p) (λ k₁ l₁ → ε k₁ (stem p l₁)) c₀ (inl n))
                    =⟨ graft-node-from-to (δ _ p) (λ k l → ε k (stem p l)) c₀ (inl n) ⟩ 
                  inl n ∎

    graft-node-from-to (nd (c , δ)) ε c₀ (inr (k , stem p l , n)) with
      (graft-node-from (δ _ p) (λ k l → ε k (stem p l)) c₀ ∘ graft-node-to (δ _ p) (λ k l → ε k (stem p l)) c₀) (inr (k , l , n))
      | inspect (graft-node-from (δ _ p) (λ k l → ε k (stem p l)) c₀ ∘ graft-node-to (δ _ p) (λ k l → ε k (stem p l)) c₀) (inr (k , l , n))
    graft-node-from-to (nd (c , δ)) ε c₀ (inr (k , stem p l , n)) | inl n' | ingraph e =
      ⊥-elim (inl≠inr n' (k , l , n) lem)

      where lem = inl n' =⟨ ! e ⟩
                  graft-node-from (δ _ p) (λ k l → ε k (stem p l)) c₀
                    (graft-node-to (δ _ p) (λ k l → ε k (stem p l)) c₀ (inr (k , l , n)))
                    =⟨ graft-node-from-to (δ _ p) (λ k l → ε k (stem p l)) c₀ (inr (k , l , n)) ⟩
                  inr (k , l , n) ∎

    graft-node-from-to (nd (c , δ)) ε c₀ (inr (k , stem p l , n)) | inr (k' , l' , n') | ingraph e =
      let lem' = –> (inr=inr-equiv (k' , l' , n') (k , l , n)) lem
      in ap inr (pair= (fst= lem') (apd↓-cst (λ x → (stem p (fst x) , snd x)) (snd= lem')))

      where lem = inr (k' , l' , n') =⟨ ! e ⟩ 
                  graft-node-from (δ _ p) (λ k l → ε k (stem p l)) c₀
                    (graft-node-to (δ _ p) (λ k l → ε k (stem p l)) c₀ (inr (k , l , n)))
                    =⟨ graft-node-from-to (δ _ p) (λ k l → ε k (stem p l)) c₀ (inr (k , l , n)) ⟩ 
                  inr (k , l , n) ∎
      
    graft-node-eqv : {i : I} (w : W P i)
      → (ε : ∀ j → Leaf P w j → W P j)
      → {j : I} (c : γ P j)
      → Node P w c ⊔ Σ I (λ k → Σ (Leaf P w k) (λ l → Node P (ε k l) c))
        ≃ Node P (graft w ε) c
    graft-node-eqv w ε c =
      equiv (graft-node-to w ε c) (graft-node-from w ε c)
            (graft-node-to-from w ε c) (graft-node-from-to w ε c)

  --
  --  Frames and FillingFamilies
  --
  
  Frame : {I : Type₀} (P : Poly I) {i : I} (w : W P i) (c : γ P i) → Type₀
  Frame {I} P w c = (j : I) → Leaf P w j ≃ ρ P c j

  FillingFamily : {I : Type₀} → Poly I → Type₁
  FillingFamily {I} P = {i : I} {w : W P i} {c : γ P i} → Frame P w c → Type₀

  _//_ : {I : Type₀} (P : Poly I) (F : FillingFamily P) → Poly (Σ I (γ P))
  γ (P // F) (i , c) = Σ (W P i) (λ w → Σ (Frame P w c) F)
  ρ (P // F) (w , f , x) (j , d) = Node P w d

  --
  --  The Baez-Dolan substitution operation
  --

  module Substitution {I : Type₀} {P : Poly I} (F : FillingFamily P) where

    {-# TERMINATING #-}
    flatten : {i : I} (c : γ P i)
      → (tr : W (P // F) (i , c))
      → W P i

    -- The flattened tree has a canonical c-frame
    flatten-frm : {i : I} (c : γ P i)
      → (tr : W (P // F) (i , c))
      → (j : I) → Leaf P (flatten c tr) j ≃ ρ P c j

    substitute : {i : I} (w : W P i)
      → (κ : (c : Σ I (γ P)) → Node P w (snd c) → W (P // F) c)
      → W P i

    -- A substituted tree has the same leaves
    substitute-lf-eqv : {i : I} (w : W P i)
      → (κ : (c : Σ I (γ P)) → Node P w (snd c) → W (P // F) c)
      → (j : I) → Leaf P (substitute w κ) j ≃ Leaf P w j

    flatten c (lf .(_ , c)) = corolla P c
    flatten c (nd ((w , f , x) , ε)) = substitute w ε

    flatten-frm c (lf .(_ , c)) j = corolla-lf-eqv P c j
    flatten-frm c (nd ((w , f , x) , ε)) j = f j ∘e substitute-lf-eqv w ε j

    substitute (lf i) κ = lf i
    substitute (nd {i} (c , δ)) κ =
      let tr = κ (i , c) this
          p j l = –> (flatten-frm c tr j) l
          ε j l = substitute (δ j (p j l)) (λ ic n → κ ic (that (p j l) n))
      in graft P (flatten c tr) ε 

    substitute-lf-eqv (lf i) κ j = ide (Leaf P (lf i) j)
    substitute-lf-eqv (nd {i} (c , δ)) κ j =
      let tr = κ (i , c) this 
          p j l = –> (flatten-frm c tr j) l
          κ' j l ic n = κ ic (that (p j l) n)
          ε j l = substitute (δ j (p j l)) (κ' j l) 
      in nd-lf-eqv P c δ j ∘e
         Σ-emap-r (λ k → Σ-emap-l (λ p → Leaf P (δ k p) j) (flatten-frm c tr k) ∘e
                         Σ-emap-r (λ l → substitute-lf-eqv (δ k (p k l)) (κ' k l) j)) ∘e
         graft-leaf-eqv P (flatten c tr) ε j

    bd-frame : {i : I} (c : γ P i)
      → (tr : W (P // F) (i , c))
      → (jd : Σ I (γ P)) → Leaf (P // F) tr jd ≃ Node P (flatten c tr) (snd jd)

    substitute-nd-eqv : {i : I} (w : W P i)
      → (κ : (c : Σ I (γ P)) → Node P w (snd c) → W (P // F) c)
      → (jd : Σ I (γ P))
      → Σ (Σ I (γ P)) (λ ke → Σ (Node P w (snd ke)) (λ n → Leaf (P // F) (κ ke n) jd))
        ≃ Node P (substitute w κ) (snd jd) 

    lf-corolla-eqv : {i j : I} (c : γ P i) (d : γ P j)
      → Leaf (P // F) (lf (i , c)) (j , d)
        ≃ Node P (nd (c , λ k p → lf k)) d
    lf-corolla-eqv {i} {j} c d = equiv to from to-from from-to

      where to : Leaf (P // F) (lf (i , c)) (j , d) → Node P (nd (c , λ k p → lf k)) d
            to (leaf .(_ , _)) = this

            from : Node P (nd (c , λ k p → lf k)) d → Leaf (P // F) (lf (i , c)) (j , d)
            from this = leaf (i , c)
            from (that p ())

            to-from : (n : Node P (nd (c , λ k p → lf k)) d) → to (from n) == n
            to-from this = idp
            to-from (that p ())
            
            from-to : (l : Leaf (P // F) (lf (i , c)) (j , d)) → from (to l) == l
            from-to (leaf .(_ , _)) = idp
            
    bd-frame c (lf .(_ , c)) (j , d) = lf-corolla-eqv c d 
    bd-frame c (nd ((w , f , x) , ε)) (j , d) =
      substitute-nd-eqv w ε (j , d) ∘e
      (nd-lf-eqv (P // F) (w , f , x) ε (j , d))⁻¹  

    -- A trivial, technical lemma we need in the proof below
    module SplitLemma {i : I} {c : γ P i} (δ : ∀ j → ρ P c j → W P j)
      (κ : (ic : Σ I (γ P)) → Node P (nd (c , δ)) (snd ic) → W (P // F) ic)
      {j : I} (d : γ P j) where

      A = Σ (Σ I (γ P)) (λ ke → Σ (Node P (nd (c , δ)) (snd ke)) (λ n → Leaf (P // F) (κ ke n) (j , d)))
      B = Σ I (λ k → Σ (ρ P c k) (λ p →
                 Σ (Σ I (γ P)) (λ le →
                   Σ (Node P (δ k p) (snd le)) (λ n →
                     Leaf (P // F) (κ le (that p n)) (j , d)))))

      split-to : A → Leaf (P // F) (κ (i , c) this) (j , d) ⊔ B
      split-to ((k , e) , this , l) = inl l
      split-to ((k , e) , that p n , l) = inr (_ , p , (k , e) , n , l)

      split-from : Leaf (P // F) (κ (i , c) this) (j , d) ⊔ B → A
      split-from (inl l) = _ , this , l
      split-from (inr (_ , p , (k , e) , n , l)) = ((k , e) , that p n , l)

      split-to-from : (l : Leaf (P // F) (κ (i , c) this) (j , d) ⊔ B) →
        split-to (split-from l) == l
      split-to-from (inl l) = idp
      split-to-from (inr (_ , p , (k , e) , n , l)) = idp

      split-from-to : (a : A) → split-from (split-to a) == a
      split-from-to ((k , e) , this , l) = idp
      split-from-to ((k , e) , that p n , l) = idp

      split-eqv : A ≃ Leaf (P // F) (κ (i , c) this) (j , d) ⊔ B
      split-eqv = equiv split-to split-from split-to-from split-from-to

    {-# TERMINATING #-}
    substitute-nd-eqv (lf i) κ (j , d) =
      equiv (λ { (_ , () , _) }) (λ { () }) (λ { () }) λ { (_ , () , _) }
    substitute-nd-eqv (nd {i} (c , δ)) κ (j , d) = 
      let open SplitLemma δ κ d
          tr = κ (i , c) this 
          p j l = –> (flatten-frm c tr j) l
          κ' j l ic n = κ ic (that (p j l) n)
          ε j l = substitute (δ j (p j l)) (κ' j l) 
      in graft-node-eqv P (flatten c tr) ε d ∘e
         ⊔-emap (bd-frame c (κ (i , c) this) (j , d))
           (Σ-emap-r (λ k → (Σ-emap-r (λ l → substitute-nd-eqv (δ k (p k l)) (κ' k l) (j , d))) ∘e
            Σ-emap-l (λ p → Σ (Σ I (γ P)) (λ le → Σ (Node P (δ k p) (snd le)) (λ n → Leaf (P // F) (κ le (that p n)) (j , d))))
              (flatten-frm c (κ (i , c) this) k) ⁻¹)) ∘e 
         split-eqv 

