{-# OPTIONS --without-K --rewriting --no-termination-check #-}

open import HoTT
open import Util
open import Polynomial

module Indexed {ℓ} {I : Type ℓ} (P : Poly I) where

  Sort : ℕ → Type ℓ
  SPoly : (n : ℕ) → Poly (Sort n)

  μ : (n : ℕ) {i : Sort (S n)} → W (SPoly (S n)) i → Op (SPoly (S n)) i
  μ-frm : (n : ℕ) {i : Sort (S n)} (w : W (SPoly (S n)) i) → Frame (SPoly (S n)) w (μ n w)

  Sort 0 = I
  Sort (S n) = Ops (SPoly n)
  
  SPoly O = P
  Op (SPoly (S O)) (i , f) = Σ (W P i) (λ w → Frame P w f)
  Param (SPoly (S O)) (w , _) = Node P w
  Op (SPoly (S (S n))) ((i , f) , w) = hfiber (μ n) w
  Param (SPoly (S (S n))) (w , _) = Node (SPoly (S n)) w

  --
  --  Flattening, and the associated frame
  --

  flatten : (n : ℕ) {i : Sort n} {f : Op (SPoly n) i}
    → W (SPoly (S n)) (i , f) → W (SPoly n) i

  flatten-frm-to : (n : ℕ) {i : Sort n} {f : Op (SPoly n) i}
    → (pd : W (SPoly (S n)) (i , f))
    → (j : Sort n) → Leaf (SPoly n) (flatten n pd) j → Param (SPoly n) f j

  flatten-frm-from : (n : ℕ) {i : Sort n} {f : Op (SPoly n) i}
    → (pd : W (SPoly (S n)) (i , f))
    → (j : Sort n) → Param (SPoly n) f j → Leaf (SPoly n) (flatten n pd) j 

  postulate
  
    flatten-frm-to-from : (n : ℕ) {i : Sort n} {f : Op (SPoly n) i}
      → (pd : W (SPoly (S n)) (i , f))
      → (j : Sort n) (p : Param (SPoly n) f j)
      → flatten-frm-to n pd j (flatten-frm-from n pd j p) == p

    flatten-frm-from-to : (n : ℕ) {i : Sort n} {f : Op (SPoly n) i}
      → (pd : W (SPoly (S n)) (i , f))
      → (j : Sort n) (l : Leaf (SPoly n) (flatten n pd) j )
      → flatten-frm-from n pd j (flatten-frm-to n pd j l) == l

  -- The flattened tree has a canonical frame
  flatten-frm : (n : ℕ) {i : Sort n} {f : Op (SPoly n) i}
    → (pd : W (SPoly (S n)) (i , f))
    → (j : Sort n) → Leaf (SPoly n) (flatten n pd) j ≃ Param (SPoly n) f j
  flatten-frm n pd j =
    equiv (flatten-frm-to n pd j) (flatten-frm-from n pd j)
          (flatten-frm-to-from n pd j) (flatten-frm-from-to n pd j)

  --
  --  Substituting, and the equivalence of leaves
  --

  substitute : (n : ℕ) {i : Sort n} (w : W (SPoly n) i)
    → (κ : (g : Ops (SPoly n)) → Node (SPoly n) w g → W (SPoly (S n)) g)
    → W (SPoly n) i

  substitute-lf-to : (n : ℕ) {i : Sort n} (w : W (SPoly n) i)
    → (κ : (g : Ops (SPoly n)) → Node (SPoly n) w g → W (SPoly (S n)) g)
    → (j : Sort n) → Leaf (SPoly n) (substitute n w κ) j → Leaf (SPoly n) w j

  substitute-lf-from : (n : ℕ) {i : Sort n} (w : W (SPoly n) i)
    → (κ : (g : Ops (SPoly n)) → Node (SPoly n) w g → W (SPoly (S n)) g)
    → (j : Sort n) → Leaf (SPoly n) w j → Leaf (SPoly n) (substitute n w κ) j 

  postulate
  
    substitute-lf-to-from : (n : ℕ) {i : Sort n} (w : W (SPoly n) i)
      → (κ : (g : Ops (SPoly n)) → Node (SPoly n) w g → W (SPoly (S n)) g)
      → (j : Sort n) (l : Leaf (SPoly n) w j)
      → substitute-lf-to n w κ j (substitute-lf-from n w κ j l) == l

    substitute-lf-from-to : (n : ℕ) {i : Sort n} (w : W (SPoly n) i)
      → (κ : (g : Ops (SPoly n)) → Node (SPoly n) w g → W (SPoly (S n)) g)
      → (j : Sort n) (l : Leaf (SPoly n) (substitute n w κ) j)
      → substitute-lf-from n w κ j (substitute-lf-to n w κ j l) == l

  -- A substituted tree has the same leaves
  substitute-lf-eqv : (n : ℕ) {i : Sort n} (w : W (SPoly n) i)
    → (κ : (g : Ops (SPoly n)) → Node (SPoly n) w g → W (SPoly (S n)) g)
    → (j : Sort n) → Leaf (SPoly n) (substitute n w κ) j ≃ Leaf (SPoly n) w j
  substitute-lf-eqv n w κ j = 
    equiv (substitute-lf-to n w κ j) (substitute-lf-from n w κ j)
          (substitute-lf-to-from n w κ j) (substitute-lf-from-to n w κ j)

  --
  --  Implementation
  --

  flatten n (lf (i , f)) = corolla (SPoly n) f
  flatten O (nd ((w , α) , κ)) = substitute 0 w κ
  flatten (S n) (nd ((w , e) , κ)) = substitute (S n) w κ

  flatten-frm-to n (lf .(_ , _)) j (_ , p , idp) = p
  flatten-frm-to O (nd ((w , α) , κ)) j l = 
    –> (α j) (substitute-lf-to 0 w κ j l) 
  flatten-frm-to (S n) (nd ((w , idp) , κ)) j l =
    –> (μ-frm n w j) (substitute-lf-to (S n) w κ j l)

  flatten-frm-from n (lf .(_ , _)) j p = j , p , idp
  flatten-frm-from O (nd ((w , α) , κ)) j p = 
    substitute-lf-from 0 w κ j (<– (α j) p)
  flatten-frm-from (S n) (nd ((w , idp) , κ)) j p =
    substitute-lf-from (S n) w κ j (<– (μ-frm n w j) p)

  substitute n (lf i) κ = lf i
  substitute n (nd {i} (f , ϕ)) κ = 
    let pd = κ (i , f) (inl idp)
        p j l = flatten-frm-to n pd j l
        ε j l = substitute n (ϕ j (p j l)) (λ ic n → κ ic (inr (j , p j l , n))) 
    in graft (SPoly n) (flatten n pd) ε

  substitute-lf-to n (lf i) κ j l = l
  substitute-lf-to n (nd {i} (f , ϕ)) κ j l = 
    let pd = κ (i , f) (inl idp)
        p j l = flatten-frm-to n pd j l
        κ' j l ic n = κ ic (inr (j , p j l , n))
        ε j l = substitute n (ϕ j (p j l)) (λ ic n → κ ic (inr (j , p j l , n)))
        (k , l₀ , l₁) = graft-leaf-from (SPoly n) (flatten n pd) ε j l
        p' = flatten-frm-to n pd k l₀
        l' = substitute-lf-to n (ϕ k (p k l₀)) (κ' k l₀) j l₁
    in (k , p' , l')

  substitute-lf-from n (lf i) κ j l = l
  substitute-lf-from n (nd {i} (f , ϕ)) κ j (k , p' , ll) = 
    let pd = κ (i , f) (inl idp)
        p j l = flatten-frm-to n pd j l
        κ' j l ic n = κ ic (inr (j , p j l , n))
        ε j l = substitute n (ϕ j (p j l)) (κ' j l)
        l' = flatten-frm-from n pd k p'
        ll' = substitute-lf-from n (ϕ k p') (λ ic n → κ ic (inr (k , p' , n))) j ll
        Q x = Leaf (SPoly n) (substitute n (ϕ k x) (λ ic n → κ ic (inr (k , x , n)))) j
    in graft-leaf-to (SPoly n) (flatten n pd) ε j (k , l' , transport! Q (flatten-frm-to-from n pd k p') ll')

  --
  --  The Baez-Dolan Frame
  --
  
  bd-frame-to : (m : ℕ) {i : Sort m} {f : Op (SPoly m) i}
    → (pd : W (SPoly (S m)) (i , f)) (jg : Ops (SPoly m))
    → Leaf (SPoly (S m)) pd jg → Node (SPoly m) (flatten m pd) jg

  bd-frame-from : (m : ℕ) {i : Sort m} {f : Op (SPoly m) i}
    → (pd : W (SPoly (S m)) (i , f)) (jg : Ops (SPoly m))
    → Node (SPoly m) (flatten m pd) jg → Leaf (SPoly (S m)) pd jg
  
  postulate
  
    bd-frame-to-from : (m : ℕ) {i : Sort m} {f : Op (SPoly m) i}
      → (pd : W (SPoly (S m)) (i , f)) (jg : Ops (SPoly m))
      → (n : Node (SPoly m) (flatten m pd) jg)
      → bd-frame-to m pd jg (bd-frame-from m pd jg n) == n

    bd-frame-from-to : (m : ℕ) {i : Sort m} {f : Op (SPoly m) i}
      → (pd : W (SPoly (S m)) (i , f)) (jg : Ops (SPoly m))
      → (l : Leaf (SPoly (S m)) pd jg)
      → bd-frame-from m pd jg (bd-frame-to m pd jg l) == l

  bd-frame : (m : ℕ) {i : Sort m} {f : Op (SPoly m) i}
    → (pd : W (SPoly (S m)) (i , f))
    → (jg : Ops (SPoly m)) → Leaf (SPoly (S m)) pd jg ≃ Node (SPoly m) (flatten m pd) jg
  bd-frame m pd jg = equiv (bd-frame-to m pd jg) (bd-frame-from m pd jg)
    (bd-frame-to-from m pd jg) (bd-frame-from-to m pd jg)

  --
  --  Nodes in a substituted tree
  --

  substitute-nd-to : (m : ℕ) {i : Sort m} (w : W (SPoly m) i)
    → (κ : (g : Ops (SPoly m)) → Node (SPoly m) w g → W (SPoly (S m)) g) (jg : Ops (SPoly m))
    → Σ (Ops (SPoly m)) (λ ke → Σ (Node (SPoly m) w ke) (λ n → Leaf (SPoly (S m)) (κ ke n) jg))
    → Node (SPoly m) (substitute m w κ) jg 

  substitute-nd-from : (m : ℕ) {i : Sort m} (w : W (SPoly m) i)
    → (κ : (g : Ops (SPoly m)) → Node (SPoly m) w g → W (SPoly (S m)) g) (jg : Ops (SPoly m))
    → Node (SPoly m) (substitute m w κ) jg 
    → Σ (Ops (SPoly m)) (λ ke → Σ (Node (SPoly m) w ke) (λ n → Leaf (SPoly (S m)) (κ ke n) jg))

  postulate
  
    substitute-nd-to-from : (m : ℕ) {i : Sort m} (w : W (SPoly m) i)
      → (κ : (g : Ops (SPoly m)) → Node (SPoly m) w g → W (SPoly (S m)) g) (jg : Ops (SPoly m))
      → (n : Node (SPoly m) (substitute m w κ) jg)
      → substitute-nd-to m w κ jg (substitute-nd-from m w κ jg n) == n

    substitute-nd-from-to : (m : ℕ) {i : Sort m} (w : W (SPoly m) i)
      → (κ : (g : Ops (SPoly m)) → Node (SPoly m) w g → W (SPoly (S m)) g) (jg : Ops (SPoly m))
      → (t : Σ (Ops (SPoly m)) (λ ke → Σ (Node (SPoly m) w ke) (λ n → Leaf (SPoly (S m)) (κ ke n) jg)))
      → substitute-nd-from m w κ jg (substitute-nd-to m w κ jg t) == t

  substitute-nd-eqv : (m : ℕ) {i : Sort m} (w : W (SPoly m) i)
    → (κ : (g : Ops (SPoly m)) → Node (SPoly m) w g → W (SPoly (S m)) g)
    → (jg : Ops (SPoly m))
    → Σ (Ops (SPoly m)) (λ ke → Σ (Node (SPoly m) w ke) (λ n → Leaf (SPoly (S m)) (κ ke n) jg))
    ≃ Node (SPoly m) (substitute m w κ) jg 
  substitute-nd-eqv m w κ jg =
    equiv (substitute-nd-to m w κ jg) (substitute-nd-from m w κ jg)
          (substitute-nd-to-from m w κ jg) (substitute-nd-from-to m w κ jg)
  
  --
  --  Implementation
  --


  bd-frame-to m (lf .(j , g)) (j , g) idp = (inl idp)
  bd-frame-to O (nd ((w , α) , κ)) = substitute-nd-to 0 w κ
  bd-frame-to (S m) (nd ((w , e) , κ)) = substitute-nd-to (S m) w κ
  
  bd-frame-from m (lf .(j , g)) (j , g) (inl idp) = idp
  bd-frame-from m (lf .(_ , _)) (j , g) (inr (_ , p , ()))
  bd-frame-from 0 (nd ((w , α) , κ)) = substitute-nd-from 0 w κ 
  bd-frame-from (S m) (nd ((w , e) , κ)) = substitute-nd-from (S m) w κ 

  substitute-nd-to m (lf i) κ (j , g) ((k , e) , () , l)
  substitute-nd-to m (nd (f , ϕ)) κ (j , g) ((k , .f) , (inl idp) , l) = 
    let pd = κ (k , f) (inl idp) 
        p j l = flatten-frm-to m pd j l
        κ' j l ic n = κ ic (inr (j , p j l , n))
        ε j l = substitute m (ϕ j (p j l)) (κ' j l) 
    in graft-node-to (SPoly m) (flatten m pd) ε (j , g) (inl (bd-frame-to m pd (j , g) l))
  substitute-nd-to m (nd {i} (f , ϕ)) κ (j , g) ((k , e) , (inr (a , p' , n)) , l) = 
    let pd = κ (i , f) (inl idp) 
        p j l = flatten-frm-to m pd j l
        κ' j l ic n = κ ic (inr (j , p j l , n))
        ε j l = substitute m (ϕ j (p j l)) (κ' j l)
        l' = flatten-frm-from m pd a p'
        Q x = Node (SPoly m) (substitute m (ϕ a x) (λ ic n → κ ic (inr (a , x , n)))) (j , g)
        n' = substitute-nd-to m (ϕ a p') (λ ic n₀ → κ ic (inr (a , p' , n₀))) (j , g) ((k , e) , n , l)
    in graft-node-to (SPoly m) (flatten m pd) ε (j , g) (inr (a , l' , transport! Q (flatten-frm-to-from m pd a p') n' ))

  substitute-nd-from m (lf i) κ (j , g) ()
  substitute-nd-from m (nd {i} (f , ϕ)) κ (j , g) n with graft-node-from (SPoly m) (flatten m (κ (i , f) (inl idp))) _ (j , g) n
  substitute-nd-from m (nd {i} (f , ϕ)) κ (j , g) n | inl n' =
    (i , f) , (inl idp) , (bd-frame-from m (κ (i , f) (inl idp)) (j , g) n')
  substitute-nd-from m (nd {i} (f , ϕ)) κ (j , g) n | inr (k , l' , n') = 
    let pd = κ (i , f) (inl idp) 
        p j l = flatten-frm-to m pd j l
        κ' j l ic n = κ ic (inr (j , p j l , n))
        ε j l = substitute m (ϕ j (p j l)) (κ' j l)
        p' = flatten-frm-to m pd k l'
        (ke , n'' , l'') = substitute-nd-from m (ϕ k p') (λ ic n₀ → κ ic (inr (k , p' , n₀))) (j , g) n'
    in ke , (inr (k , p' , n'')) , l''
    

  --
  --  Monad multiplication
  --

  μ O w = flatten 0 w , flatten-frm 0 w
  μ (S n) {(i , f) , o} w = flatten (S n) w , {!!}
  
  μ-frm O w = bd-frame 0 w
  μ-frm (S n) {(i , f) , o} w = bd-frame (S n) w
