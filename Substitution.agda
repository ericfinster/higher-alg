{-# OPTIONS --without-K --rewriting --no-termination-check #-}

open import HoTT
open import Util
open import Polynomial

-- The postulates here can all be proved (see previous incarnations of
-- this library), however, they tend to seriously bog down typechecking.
-- Since we thus want to abstract them anyway, we leave them as
-- postulates here.

module Substitution {ℓ} {I : Type ℓ} {P : Poly I} (R : Relator P) where

  --
  --  Flattening, and the associated frame
  --

  flatten : {i : I} {f : Op P i} (pd : W (P // R) (i , f)) → W P i

  flatten-frm-to : {i : I} {f : Op P i}
    → (pd : W (P // R) (i , f))
    → (j : I) → Leaf P (flatten pd) j → Param P f j

  flatten-frm-from : {i : I} {f : Op P i}
    → (pd : W (P // R) (i , f))
    → (j : I) → Param P f j → Leaf P (flatten pd) j 

  postulate
  
    flatten-frm-to-from : {i : I} {f : Op P i}
      → (pd : W (P // R) (i , f))
      → (j : I) (p : Param P f j)
      → flatten-frm-to pd j (flatten-frm-from pd j p) == p

    flatten-frm-from-to : {i : I} {f : Op P i}
      → (pd : W (P // R) (i , f))
      → (j : I) (l : Leaf P (flatten pd) j )
      → flatten-frm-from pd j (flatten-frm-to pd j l) == l

  -- The flattened tree has a canonical c-frame
  flatten-frm : {i : I} {f : Op P i}
    → (pd : W (P // R) (i , f))
    → (j : I) → Leaf P (flatten pd) j ≃ Param P f j

  --
  --  Substituting, and the equivalence of leaves
  --

  substitute : {i : I} (w : W P i)
    → (κ : (c : Σ I (Op P)) → Node P w (snd c) → W (P // R) c)
    → W P i

  substitute-lf-to : {i : I} (w : W P i)
    → (κ : (c : Σ I (Op P)) → Node P w (snd c) → W (P // R) c)
    → (j : I) → Leaf P (substitute w κ) j → Leaf P w j

  substitute-lf-from : {i : I} (w : W P i)
    → (κ : (c : Σ I (Op P)) → Node P w (snd c) → W (P // R) c)
    → (j : I) → Leaf P w j → Leaf P (substitute w κ) j 

  postulate
  
    substitute-lf-to-from : {i : I} (w : W P i)
      → (κ : (c : Σ I (Op P)) → Node P w (snd c) → W (P // R) c)
      → (j : I) (l : Leaf P w j)
      → substitute-lf-to w κ j (substitute-lf-from w κ j l) == l

    substitute-lf-from-to : {i : I} (w : W P i)
      → (κ : (c : Σ I (Op P)) → Node P w (snd c) → W (P // R) c)
      → (j : I) (l : Leaf P (substitute w κ) j)
      → substitute-lf-from w κ j (substitute-lf-to w κ j l) == l

  -- A substituted tree has the same leaves
  substitute-lf-eqv : {i : I} (w : W P i)
    → (κ : (c : Σ I (Op P)) → Node P w (snd c) → W (P // R) c)
    → (j : I) → Leaf P (substitute w κ) j ≃ Leaf P w j

  --
  --  Implementation
  --

  flatten (lf (i , f)) = corolla P f
  flatten (nd ((w , α , r) , κ)) = substitute w κ

  flatten-frm-to (lf _) j (_ , p , idp) = p
  flatten-frm-to (nd ((w , α , r) , κ)) j l = –> (α j) (substitute-lf-to w κ j l)
  
  flatten-frm-from (lf (i , f)) j p = (j , p , idp)
  flatten-frm-from (nd ((w , α , r) , κ)) j p = substitute-lf-from w κ j (<– (α j) p)
  
  flatten-frm pd j =
    equiv (flatten-frm-to pd j) (flatten-frm-from pd j)
          (flatten-frm-to-from pd j) (flatten-frm-from-to pd j)

  substitute (lf i) κ = lf i
  substitute (nd {i} (f , ϕ)) κ = 
    let pd = κ (i , f) (inl idp)
        p j l = flatten-frm-to pd j l
        ε j l = substitute (ϕ j (p j l)) (λ ic n → κ ic (inr (j , p j l , n)))
    in graft P (flatten pd) ε 

  substitute-lf-to (lf i) κ j l = l
  substitute-lf-to (nd {i} (f , ϕ)) κ j l = 
    let pd = κ (i , f) (inl idp)
        p j l = flatten-frm-to pd j l
        κ' j l ic n = κ ic (inr (j , p j l , n))
        ε j l = substitute (ϕ j (p j l)) (λ ic n → κ ic (inr (j , p j l , n)))
        (k , l₀ , l₁) = graft-leaf-to P (flatten pd) ε j l
        p' = flatten-frm-to pd k l₀
        l' = substitute-lf-to (ϕ k (p k l₀)) (κ' k l₀) j l₁
    in (k , p' , l')

  substitute-lf-from (lf i) κ j l = l
  substitute-lf-from (nd {i} (f , ϕ)) κ j (k , p' , ll) = 
    let pd = κ (i , f) (inl idp)
        p j l = flatten-frm-to pd j l
        κ' j l ic n = κ ic (inr (j , p j l , n))
        ε j l = substitute (ϕ j (p j l)) (κ' j l)
        l' = flatten-frm-from pd k p'
        ll' = substitute-lf-from (ϕ k p') (λ ic n → κ ic (inr (k , p' , n))) j ll
        Q x = Leaf P (substitute (ϕ k x) (λ ic n → κ ic (inr (k , x , n)))) j
    in graft-leaf-from P (flatten pd) ε j (k , l' , transport! Q (flatten-frm-to-from pd k p') ll')

  substitute-lf-eqv w κ j =
    equiv (substitute-lf-to w κ j) (substitute-lf-from w κ j)
          (substitute-lf-to-from w κ j) (substitute-lf-from-to w κ j)

  --
  --  The Baez-Dolan Frame
  --
  
  bd-frame-to : {i : I} {f : Op P i}
    → (pd : W (P // R) (i , f)) (jd : Σ I (Op P))
    → Leaf (P // R) pd jd → Node P (flatten pd) (snd jd)

  bd-frame-from : {i : I} {f : Op P i}
    → (pd : W (P // R) (i , f)) (jd : Σ I (Op P))
    → Node P (flatten pd) (snd jd) → Leaf (P // R) pd jd

  postulate
  
    bd-frame-to-from : {i : I} {f : Op P i}
      → (pd : W (P // R) (i , f)) (jd : Σ I (Op P))
      → (n : Node P (flatten pd) (snd jd))
      → bd-frame-to pd jd (bd-frame-from pd jd n) == n

    bd-frame-from-to : {i : I} {f : Op P i}
      → (pd : W (P // R) (i , f)) (jd : Σ I (Op P))
      → (l : Leaf (P // R) pd jd)
      → bd-frame-from pd jd (bd-frame-to pd jd l) == l

  bd-frame : {i : I} {f : Op P i}
    → (pd : W (P // R) (i , f))
    → (jd : Σ I (Op P)) → Leaf (P // R) pd jd ≃ Node P (flatten pd) (snd jd)

  --
  --  Nodes in a substituted tree
  --

  substitute-nd-to : {i : I} (w : W P i)
    → (κ : (c : Σ I (Op P)) → Node P w (snd c) → W (P // R) c) (jd : Σ I (Op P))
    → Σ (Σ I (Op P)) (λ ke → Σ (Node P w (snd ke)) (λ n → Leaf (P // R) (κ ke n) jd))
    → Node P (substitute w κ) (snd jd) 

  substitute-nd-from : {i : I} (w : W P i)
    → (κ : (c : Σ I (Op P)) → Node P w (snd c) → W (P // R) c) (jd : Σ I (Op P))
    → Node P (substitute w κ) (snd jd) 
    → Σ (Σ I (Op P)) (λ ke → Σ (Node P w (snd ke)) (λ n → Leaf (P // R) (κ ke n) jd))

  postulate
  
    substitute-nd-to-from : {i : I} (w : W P i)
      → (κ : (c : Σ I (Op P)) → Node P w (snd c) → W (P // R) c) (jd : Σ I (Op P))
      → (n : Node P (substitute w κ) (snd jd))
      → substitute-nd-to w κ jd (substitute-nd-from w κ jd n) == n

    substitute-nd-from-to : {i : I} (w : W P i)
      → (κ : (c : Σ I (Op P)) → Node P w (snd c) → W (P // R) c) (jd : Σ I (Op P))
      → (t : Σ (Σ I (Op P)) (λ ke → Σ (Node P w (snd ke)) (λ n → Leaf (P // R) (κ ke n) jd)))
      → substitute-nd-from w κ jd (substitute-nd-to w κ jd t) == t

  substitute-nd-eqv : {i : I} (w : W P i)
    → (κ : (c : Σ I (Op P)) → Node P w (snd c) → W (P // R) c)
    → (jd : Σ I (Op P))
    → Σ (Σ I (Op P)) (λ ke → Σ (Node P w (snd ke)) (λ n → Leaf (P // R) (κ ke n) jd))
    ≃ Node P (substitute w κ) (snd jd) 

  --
  --  Implementation
  --

  bd-frame-to (lf .(j , g)) (j , g) idp = (inl idp)
  bd-frame-to (nd ((w , α , r) , κ)) (j , g) (k , p , l) =
    substitute-nd-to w κ (j , g) (k , p , l)
  
  bd-frame-from (lf .(j , g)) (j , g) (inl idp) = idp
  bd-frame-from (lf .(_ , _)) (j , g) (inr (_ , p , ()))
  bd-frame-from (nd ((w , α , r) , κ)) (j , g) n =
    substitute-nd-from w κ (j , g) n
    
  bd-frame pd jd =
    equiv (bd-frame-to pd jd) (bd-frame-from pd jd)
          (bd-frame-to-from pd jd) (bd-frame-from-to pd jd)

  substitute-nd-to (lf i) κ (j , g) ((k , e) , () , l)
  substitute-nd-to (nd (f , ϕ)) κ (j , g) ((k , .f) , (inl idp) , l) = 
    let pd = κ (k , f) (inl idp) 
        p j l = flatten-frm-to pd j l
        κ' j l ic n = κ ic (inr (j , p j l , n))
        ε j l = substitute (ϕ j (p j l)) (κ' j l) 
    in graft-node-to P (flatten pd) ε g (inl (bd-frame-to pd (j , g) l))
    
  substitute-nd-to (nd {i} (f , ϕ)) κ (j , g) ((k , e) , (inr (a , p' , n)) , l) = 
    let pd = κ (i , f) (inl idp) 
        p j l = flatten-frm-to pd j l
        κ' j l ic n = κ ic (inr (j , p j l , n))
        ε j l = substitute (ϕ j (p j l)) (κ' j l)
        l' = flatten-frm-from pd a p'
        Q x = Node P (substitute (ϕ a x) (λ ic n → κ ic (inr (a , x , n)))) g
        n' = substitute-nd-to (ϕ a p') (λ ic n₀ → κ ic (inr (a , p' , n₀))) (j , g) ((k , e) , n , l)
    in graft-node-to P (flatten pd) ε g (inr (a , l' , transport! Q (flatten-frm-to-from pd a p') n' ))
    
  substitute-nd-from (lf i) κ (j , g) ()
  substitute-nd-from (nd {i} (f , ϕ)) κ (j , g) n with graft-node-from P (flatten (κ (i , f) (inl idp))) _ g n
  substitute-nd-from (nd {i} (f , ϕ)) κ (j , g) n | inl n' =
    (i , f) , (inl idp) , (bd-frame-from (κ (i , f) (inl idp)) (j , g) n')
  substitute-nd-from (nd {i} (f , ϕ)) κ (j , g) n | inr (k , l' , n') = 
    let pd = κ (i , f) (inl idp) 
        p j l = flatten-frm-to pd j l
        κ' j l ic n = κ ic (inr (j , p j l , n))
        ε j l = substitute (ϕ j (p j l)) (κ' j l)
        p' = flatten-frm-to pd k l'
        (ke , n'' , l'') = substitute-nd-from (ϕ k p') (λ ic n₀ → κ ic (inr (k , p' , n₀))) (j , g) n'
    in ke , (inr (k , p' , n'')) , l''
    
  substitute-nd-eqv w κ jd =
    equiv (substitute-nd-to w κ jd) (substitute-nd-from w κ jd)
          (substitute-nd-to-from w κ jd) (substitute-nd-from-to w κ jd)





