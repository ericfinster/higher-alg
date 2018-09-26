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

  flatten : (n : ℕ) {i : Sort n} {f : Op (SPoly n) i}
    → W (SPoly (S n)) (i , f) → W (SPoly n) i

  flatten-frm-to : (n : ℕ) {i : Sort n} {f : Op (SPoly n) i}
    → (pd : W (SPoly (S n)) (i , f))
    → (j : Sort n) → Leaf (SPoly n) (flatten n pd) j → Param (SPoly n) f j

  flatten-frm-from : (n : ℕ) {i : Sort n} {f : Op (SPoly n) i}
    → (pd : W (SPoly (S n)) (i , f))
    → (j : Sort n) → Param (SPoly n) f j → Leaf (SPoly n) (flatten n pd) j 

  -- postulate
  
  --   flatten-frm-to-from : {i : I} {f : Op P i}
  --     → (pd : W (P // R) (i , f))
  --     → (j : I) (p : Param P f j)
  --     → flatten-frm-to pd j (flatten-frm-from pd j p) == p

  --   flatten-frm-from-to : {i : I} {f : Op P i}
  --     → (pd : W (P // R) (i , f))
  --     → (j : I) (l : Leaf P (flatten pd) j )
  --     → flatten-frm-from pd j (flatten-frm-to pd j l) == l

  -- -- The flattened tree has a canonical frame
  -- flatten-frm : {i : I} {f : Op P i}
  --   → (pd : W (P // R) (i , f))
  --   → (j : I) → Leaf P (flatten pd) j ≃ Param P f j

  subst : (n : ℕ) {i : Sort n} (w : W (SPoly n) i)
    → (κ : (g : Ops (SPoly n)) → Node (SPoly n) w g → W (SPoly (S n)) g)
    → W (SPoly n) i


  flatten n (lf (i , f)) = corolla (SPoly n) f
  flatten O (nd ((w , α) , κ)) = subst 0 w κ
  flatten (S n) (nd ((w , e) , κ)) = subst (S n) w κ

  flatten-frm-to n (lf .(_ , _)) j (_ , p , idp) = p
  flatten-frm-to O (nd ((w , α) , κ)) j l = {!!}
  flatten-frm-to (S n) {i , f} .{μ n w} (nd ((w , idp) , κ)) j l = {!μ-frm n w!}

  -- flatten-frm-to (lf _) j (_ , p , idp) = p
  -- flatten-frm-to (nd ((w , α , r) , κ)) j l =
  --   –> (α j) (substitute-lf-to w κ j l) 

  flatten-frm-from = {!!}
  
  -- flatten-frm-from (lf (i , f)) j p = (j , p , idp)
  -- flatten-frm-from (nd ((w , α , r) , κ)) j p =
  --   substitute-lf-from w κ j (<– (α j) p)



  subst n (lf i) κ = lf i
  subst n (nd {i} (f , ϕ)) κ = 
    let pd = κ (i , f) (inl idp)
        p j l = flatten-frm-to n pd j l
        ε j l = subst n (ϕ j (p j l)) (λ ic n → κ ic (inr (j , p j l , n))) 
    in graft (SPoly n) (flatten n pd) ε




