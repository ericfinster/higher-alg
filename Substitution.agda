{-# OPTIONS --without-K --rewriting --no-termination-check #-}

open import HoTT
open import Util
open import Poly

module Substitution {I : Type₀} {P : Poly I} (F : FillingFamily P) where

  --
  --  Flattening, and the associated frame
  --

  flatten : {i : I} {c : γ P i} (pd : W (P // F) (i , c)) → W P i

  flatten-frm-to : {i : I} {c : γ P i}
    → (pd : W (P // F) (i , c))
    → (j : I) → Leaf P (flatten pd) j → ρ P c j

  flatten-frm-from : {i : I} {c : γ P i}
    → (pd : W (P // F) (i , c))
    → (j : I) → ρ P c j → Leaf P (flatten pd) j 

  postulate
  
    flatten-frm-to-from : {i : I} {c : γ P i}
      → (pd : W (P // F) (i , c))
      → (j : I) (p : ρ P c j)
      → flatten-frm-to pd j (flatten-frm-from pd j p) == p

    flatten-frm-from-to : {i : I} {c : γ P i}
      → (pd : W (P // F) (i , c))
      → (j : I) (l : Leaf P (flatten pd) j )
      → flatten-frm-from pd j (flatten-frm-to pd j l) == l

  -- The flattened tree has a canonical c-frame
  flatten-frm : {i : I} {c : γ P i}
    → (pd : W (P // F) (i , c))
    → (j : I) → Leaf P (flatten pd) j ≃ ρ P c j

  --
  --  Substituting, and the equivalence of leaves
  --

  substitute : {i : I} (w : W P i)
    → (κ : (c : Σ I (γ P)) → Node P w (snd c) → W (P // F) c)
    → W P i

  substitute-lf-to : {i : I} (w : W P i)
    → (κ : (c : Σ I (γ P)) → Node P w (snd c) → W (P // F) c)
    → (j : I) → Leaf P (substitute w κ) j → Leaf P w j

  substitute-lf-from : {i : I} (w : W P i)
    → (κ : (c : Σ I (γ P)) → Node P w (snd c) → W (P // F) c)
    → (j : I) → Leaf P w j → Leaf P (substitute w κ) j 

  postulate
  
    substitute-lf-to-from : {i : I} (w : W P i)
      → (κ : (c : Σ I (γ P)) → Node P w (snd c) → W (P // F) c)
      → (j : I) (l : Leaf P w j)
      → substitute-lf-to w κ j (substitute-lf-from w κ j l) == l

    substitute-lf-from-to : {i : I} (w : W P i)
      → (κ : (c : Σ I (γ P)) → Node P w (snd c) → W (P // F) c)
      → (j : I) (l : Leaf P (substitute w κ) j)
      → substitute-lf-from w κ j (substitute-lf-to w κ j l) == l

  -- A substituted tree has the same leaves
  substitute-lf-eqv : {i : I} (w : W P i)
    → (κ : (c : Σ I (γ P)) → Node P w (snd c) → W (P // F) c)
    → (j : I) → Leaf P (substitute w κ) j ≃ Leaf P w j

  --
  --  Implementation
  --

  flatten (lf (i , c)) = corolla P c
  flatten (nd ((w , f , x) , κ)) = substitute w κ

  flatten-frm-to (lf _) j (stem p (leaf .j)) = p
  flatten-frm-to (nd ((w , f , x) , κ)) j l = –> (f j) (substitute-lf-to w κ j l)
  
  flatten-frm-from (lf (i , c)) j p = stem p (leaf j)
  flatten-frm-from (nd ((w , f , x) , κ)) j p = substitute-lf-from w κ j (<– (f j) p)
  
  flatten-frm pd j =
    equiv (flatten-frm-to pd j) (flatten-frm-from pd j)
          (flatten-frm-to-from pd j) (flatten-frm-from-to pd j)

  substitute (lf i) κ = lf i
  substitute (nd {i} (c , δ)) κ = 
    let pd = κ (i , c) this
        p j l = flatten-frm-to pd j l
        ε j l = substitute (δ j (p j l)) (λ ic n → κ ic (that (p j l) n))
    in graft P (flatten pd) ε 

  substitute-lf-to (lf i) κ j l = l
  substitute-lf-to (nd {i} (c , δ)) κ j l = 
    let pd = κ (i , c) this
        p j l = flatten-frm-to pd j l
        κ' j l ic n = κ ic (that (p j l) n)
        ε j l = substitute (δ j (p j l)) (λ ic n → κ ic (that (p j l) n))
        (k , l₀ , l₁) = graft-leaf-to P (flatten pd) ε j l
        p' = flatten-frm-to pd k l₀
        l' = substitute-lf-to (δ k (p k l₀)) (κ' k l₀) j l₁
    in stem p' l'

  substitute-lf-from (lf i) κ j l = l
  substitute-lf-from (nd {i} (c , δ)) κ j (stem {j = k} p' ll) = 
    let pd = κ (i , c) this
        p j l = flatten-frm-to pd j l
        κ' j l ic n = κ ic (that (p j l) n)
        ε j l = substitute (δ j (p j l)) (κ' j l)
        l' = flatten-frm-from pd k p'
        ll' = substitute-lf-from (δ k p') (λ ic n → κ ic (that p' n)) j ll
        Q x = Leaf P (substitute (δ k x) (λ ic n → κ ic (that x n))) j
    in graft-leaf-from P (flatten pd) ε j (k , l' , transport! Q (flatten-frm-to-from pd k p') ll')

  substitute-lf-eqv w κ j =
    equiv (substitute-lf-to w κ j) (substitute-lf-from w κ j)
          (substitute-lf-to-from w κ j) (substitute-lf-from-to w κ j)

  -- bd-frame : {i : I} {c : γ P i}
  --   → (pd : W (P // F) (i , c))
  --   → (jd : Σ I (γ P)) → Leaf (P // F) pd jd ≃ Node P (flatten pd) (snd jd)

  -- substitute-nd-eqv : {i : I} (w : W P i)
  --   → (κ : (c : Σ I (γ P)) → Node P w (snd c) → W (P // F) c)
  --   → (jd : Σ I (γ P))
  --   → Σ (Σ I (γ P)) (λ ke → Σ (Node P w (snd ke)) (λ n → Leaf (P // F) (κ ke n) jd))
  --     ≃ Node P (substitute w κ) (snd jd) 

  -- lf-corolla-eqv : {i j : I} (c : γ P i) (d : γ P j)
  --   → Leaf (P // F) (lf (i , c)) (j , d)
  --     ≃ Node P (nd (c , λ k p → lf k)) d
  -- lf-corolla-eqv {i} {j} c d = equiv to from to-from from-to

  --   where to : Leaf (P // F) (lf (i , c)) (j , d) → Node P (nd (c , λ k p → lf k)) d
  --         to (leaf .(_ , _)) = this

  --         from : Node P (nd (c , λ k p → lf k)) d → Leaf (P // F) (lf (i , c)) (j , d)
  --         from this = leaf (i , c)
  --         from (that p ())

  --         to-from : (n : Node P (nd (c , λ k p → lf k)) d) → to (from n) == n
  --         to-from this = idp
  --         to-from (that p ())

  --         from-to : (l : Leaf (P // F) (lf (i , c)) (j , d)) → from (to l) == l
  --         from-to (leaf .(_ , _)) = idp

  -- bd-frame (lf (i , c)) (j , d) = lf-corolla-eqv c d 
  -- bd-frame (nd ((w , f , x) , ε)) (j , d) =
  --   substitute-nd-eqv w ε (j , d) ∘e
  --   (nd-lf-eqv (P // F) (w , f , x) ε (j , d))⁻¹  

  -- -- A trivial, technical lemma we need in the proof below
  -- module SplitLemma {i : I} {c : γ P i} (δ : ∀ j → ρ P c j → W P j)
  --   (κ : (ic : Σ I (γ P)) → Node P (nd (c , δ)) (snd ic) → W (P // F) ic)
  --   {j : I} (d : γ P j) where

  --   A = Σ (Σ I (γ P)) (λ ke → Σ (Node P (nd (c , δ)) (snd ke)) (λ n → Leaf (P // F) (κ ke n) (j , d)))
  --   B = Σ I (λ k → Σ (ρ P c k) (λ p →
  --              Σ (Σ I (γ P)) (λ le →
  --                Σ (Node P (δ k p) (snd le)) (λ n →
  --                  Leaf (P // F) (κ le (that p n)) (j , d)))))

  --   split-to : A → Leaf (P // F) (κ (i , c) this) (j , d) ⊔ B
  --   split-to ((k , e) , this , l) = inl l
  --   split-to ((k , e) , that p n , l) = inr (_ , p , (k , e) , n , l)

  --   split-from : Leaf (P // F) (κ (i , c) this) (j , d) ⊔ B → A
  --   split-from (inl l) = _ , this , l
  --   split-from (inr (_ , p , (k , e) , n , l)) = ((k , e) , that p n , l)

  --   split-to-from : (l : Leaf (P // F) (κ (i , c) this) (j , d) ⊔ B) →
  --     split-to (split-from l) == l
  --   split-to-from (inl l) = idp
  --   split-to-from (inr (_ , p , (k , e) , n , l)) = idp

  --   split-from-to : (a : A) → split-from (split-to a) == a
  --   split-from-to ((k , e) , this , l) = idp
  --   split-from-to ((k , e) , that p n , l) = idp

  --   split-eqv : A ≃ Leaf (P // F) (κ (i , c) this) (j , d) ⊔ B
  --   split-eqv = equiv split-to split-from split-to-from split-from-to

  -- substitute-nd-eqv (lf i) κ (j , d) =
  --   equiv (λ { (_ , () , _) }) (λ { () }) (λ { () }) λ { (_ , () , _) }
  -- substitute-nd-eqv (nd {i} (c , δ)) κ (j , d) = 
  --   let open SplitLemma δ κ d
  --       pd = κ (i , c) this 
  --       p j l = –> (flatten-frm pd j) l
  --       κ' j l ic n = κ ic (that (p j l) n)
  --       ε j l = substitute (δ j (p j l)) (κ' j l) 
  --   in graft-node-eqv P (flatten pd) ε d ∘e
  --      ⊔-emap (bd-frame (κ (i , c) this) (j , d))
  --        (Σ-emap-r (λ k → (Σ-emap-r (λ l → substitute-nd-eqv (δ k (p k l)) (κ' k l) (j , d))) ∘e
  --         Σ-emap-l (λ p → Σ (Σ I (γ P)) (λ le → Σ (Node P (δ k p) (snd le)) (λ n → Leaf (P // F) (κ le (that p n)) (j , d))))
  --           (flatten-frm (κ (i , c) this) k) ⁻¹)) ∘e 
  --      split-eqv 




