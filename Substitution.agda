{-# OPTIONS --without-K --rewriting --no-termination-check #-}

open import HoTT
open import Util
open import Poly

-- The postulates here can all be proved (see previous incarnations of
-- this library), however, they tend to seriously bog down typechecking.
-- Since we thus want to abstract them anyway, we leave them as
-- postulates here.

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

  --
  --  The Baez-Dolan Frame
  --
  
  bd-frame-to : {i : I} {c : γ P i}
    → (pd : W (P // F) (i , c)) (jd : Σ I (γ P))
    → Leaf (P // F) pd jd → Node P (flatten pd) (snd jd)

  bd-frame-from : {i : I} {c : γ P i}
    → (pd : W (P // F) (i , c)) (jd : Σ I (γ P))
    → Node P (flatten pd) (snd jd) → Leaf (P // F) pd jd

  postulate
  
    bd-frame-to-from : {i : I} {c : γ P i}
      → (pd : W (P // F) (i , c)) (jd : Σ I (γ P))
      → (n : Node P (flatten pd) (snd jd))
      → bd-frame-to pd jd (bd-frame-from pd jd n) == n

    bd-frame-from-to : {i : I} {c : γ P i}
      → (pd : W (P // F) (i , c)) (jd : Σ I (γ P))
      → (l : Leaf (P // F) pd jd)
      → bd-frame-from pd jd (bd-frame-to pd jd l) == l

  bd-frame : {i : I} {c : γ P i}
    → (pd : W (P // F) (i , c))
    → (jd : Σ I (γ P)) → Leaf (P // F) pd jd ≃ Node P (flatten pd) (snd jd)

  --
  --  Nodes in a substituted tree
  --

  substitute-nd-to : {i : I} (w : W P i)
    → (κ : (c : Σ I (γ P)) → Node P w (snd c) → W (P // F) c) (jd : Σ I (γ P))
    → Σ (Σ I (γ P)) (λ ke → Σ (Node P w (snd ke)) (λ n → Leaf (P // F) (κ ke n) jd))
    → Node P (substitute w κ) (snd jd) 

  substitute-nd-from : {i : I} (w : W P i)
    → (κ : (c : Σ I (γ P)) → Node P w (snd c) → W (P // F) c) (jd : Σ I (γ P))
    → Node P (substitute w κ) (snd jd) 
    → Σ (Σ I (γ P)) (λ ke → Σ (Node P w (snd ke)) (λ n → Leaf (P // F) (κ ke n) jd))

  postulate
  
    substitute-nd-to-from : {i : I} (w : W P i)
      → (κ : (c : Σ I (γ P)) → Node P w (snd c) → W (P // F) c) (jd : Σ I (γ P))
      → (n : Node P (substitute w κ) (snd jd))
      → substitute-nd-to w κ jd (substitute-nd-from w κ jd n) == n

    substitute-nd-from-to : {i : I} (w : W P i)
      → (κ : (c : Σ I (γ P)) → Node P w (snd c) → W (P // F) c) (jd : Σ I (γ P))
      → (t : Σ (Σ I (γ P)) (λ ke → Σ (Node P w (snd ke)) (λ n → Leaf (P // F) (κ ke n) jd)))
      → substitute-nd-from w κ jd (substitute-nd-to w κ jd t) == t

  substitute-nd-eqv : {i : I} (w : W P i)
    → (κ : (c : Σ I (γ P)) → Node P w (snd c) → W (P // F) c)
    → (jd : Σ I (γ P))
    → Σ (Σ I (γ P)) (λ ke → Σ (Node P w (snd ke)) (λ n → Leaf (P // F) (κ ke n) jd))
    ≃ Node P (substitute w κ) (snd jd) 

  --
  --  Implementation
  --

  bd-frame-to (lf .(j , d)) (j , d) (leaf .(j , d)) = this
  bd-frame-to (nd ((w , f , x) , κ)) (j , d) (stem p l) =
    substitute-nd-to w κ (j , d) (_ , p , l)
  
  bd-frame-from (lf .(j , d)) (j , d) this = leaf (j , d)
  bd-frame-from (lf .(_ , _)) (j , d) (that p ())
  bd-frame-from (nd ((w , f , x) , κ)) (j , d) n = 
    let (i , n' , l') = substitute-nd-from w κ (j , d) n
    in stem n' l'
    
  bd-frame pd jd =
    equiv (bd-frame-to pd jd) (bd-frame-from pd jd)
          (bd-frame-to-from pd jd) (bd-frame-from-to pd jd)


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

  substitute-nd-to (lf i) κ (j , d) ((k , e) , () , l)
  substitute-nd-to (nd (c , δ)) κ (j , d) ((k , .c) , this , l) = 
    let pd = κ (k , c) this 
        p j l = flatten-frm-to pd j l
        κ' j l ic n = κ ic (that (p j l) n)
        ε j l = substitute (δ j (p j l)) (κ' j l) 
    in graft-node-to P (flatten pd) ε d (inl (bd-frame-to pd (j , d) l))
    
  substitute-nd-to (nd {i} (c , δ)) κ (j , d) ((k , e) , that {j = a} p' n , l) = 
    let pd = κ (i , c) this 
        p j l = flatten-frm-to pd j l
        κ' j l ic n = κ ic (that (p j l) n)
        ε j l = substitute (δ j (p j l)) (κ' j l)
        l' = flatten-frm-from pd a p'
        Q x = Node P (substitute (δ a x) (λ ic n → κ ic (that x n))) d
        n' = substitute-nd-to (δ a p') (λ ic n₀ → κ ic (that p' n₀)) (j , d) ((k , e) , n , l)
    in graft-node-to P (flatten pd) ε d (inr (a , l' , transport! Q (flatten-frm-to-from pd a p') n' ))
    
  substitute-nd-from (lf i) κ (j , d) ()
  substitute-nd-from (nd {i} (c , δ)) κ (j , d) n = {!!}
  
  substitute-nd-eqv w κ jd =
    equiv (substitute-nd-to w κ jd) (substitute-nd-from w κ jd)
          (substitute-nd-to-from w κ jd) (substitute-nd-from-to w κ jd)





