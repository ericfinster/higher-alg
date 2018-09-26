{-# OPTIONS --without-K --rewriting --no-termination-check #-}

open import HoTT
open import Util
open import Polynomial

module Indexed {ℓ} {I : Type ℓ} (P : Poly I) where

  Sort : ℕ → Type ℓ
  SPoly : (n : ℕ) → Poly (Sort n)

  postulate
  
    -- The hypothetical multiplication
    μ : (n : ℕ) {i : Sort (S n)} → W (SPoly (S n)) i → Op (SPoly (S n)) i

    -- It's associated frame ...
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



