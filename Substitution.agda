{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial

module Substitution {ℓ} {I : Type ℓ} (P : Poly I) where

  -- The substitution polynomial
  Subst : Poly (Ops P)
  Op Subst (i , f) = Σ (W P i) (λ w → Frame P w f)
  Param Subst (w , _) = Node P w

  -- Elementary substitution.
  subst : {i : I} (w : W P i)
    → (κ : (g : Ops P) → Node P w g → Op Subst g)
    → W P i
  subst (lf i) κ = lf i
  subst (nd (f , ϕ)) κ =
    let (w , α) = κ (_ , f) (inl idp)
        κ' j l g n = κ g (inr (j , –> (α j) l , n))
        ψ j l = subst (ϕ j (–> (α j) l)) (κ' j l)
    in graft P w ψ

  -- Leaves in a substitution
  subst-lf-to : {i : I} (w : W P i)
    → (κ : (g : Ops P) → Node P w g → Op Subst g)
    → (j : I) → Leaf P (subst w κ) j → Leaf P w j
  subst-lf-to (lf i) κ j l = l
  subst-lf-to (nd (f , ϕ)) κ j l = 
    let (w , α) = κ (_ , f) (inl idp)
        κ' j l g n = κ g (inr (j , –> (α j) l , n))
        ψ j l = subst (ϕ j (–> (α j) l)) (κ' j l)
        (k , l₀ , l₁) = graft-leaf-from P w ψ j l
    in k , –> (α k) l₀ , subst-lf-to (ϕ k (–> (α k) l₀)) (κ' k l₀) j l₁ 
    
  subst-lf-from : {i : I} (w : W P i)
    → (κ : (g : Ops P) → Node P w g → Op Subst g)
    → (j : I) → Leaf P w j → Leaf P (subst w κ) j 
  subst-lf-from (lf i) κ j l = l
  subst-lf-from (nd (f , ϕ)) κ j (k , p , l) = 
    let (w , α) = κ (_ , f) (inl idp)
        κ' j l g n = κ g (inr (j , –> (α j) l , n))
        ψ j l = subst (ϕ j (–> (α j) l)) (κ' j l)
        l' = subst-lf-from (ϕ k p) (λ g n → κ g (inr (k , p , n))) j l
        Q x = Leaf P (subst (ϕ k x) (λ g n → κ g (inr (k , x , n)))) j
    in graft-leaf-to P w ψ j (k , <– (α k) p , transport! Q (<–-inv-r (α k) p) l')

  postulate

    subst-lf-to-from : {i : I} (w : W P i)
      → (κ : (g : Ops P) → Node P w g → Op Subst g)
      → (j : I) (l : Leaf P w j)
      → subst-lf-to w κ j (subst-lf-from w κ j l) == l
      
    subst-lf-from-to : {i : I} (w : W P i)
      → (κ : (g : Ops P) → Node P w g → Op Subst g)
      → (j : I) (l : Leaf P (subst w κ) j)
      → subst-lf-from w κ j (subst-lf-to w κ j l) == l

  subst-lf-eqv : {i : I} (w : W P i)
    → (κ : (g : Ops P) → Node P w g → Op Subst g)
    → (j : I) → Leaf P (subst w κ) j ≃ Leaf P w j
  subst-lf-eqv w κ j = equiv (subst-lf-to w κ j) (subst-lf-from w κ j)
    (subst-lf-to-from w κ j) (subst-lf-from-to w κ j)

  -- Nodes in a substitution

  subst-nd-to : {i : I} (w : W P i)
    → (κ : (g : Ops P) → Node P w g → Op Subst g)
    → (g : Ops P) → Node P (subst w κ) g
    → Σ (Ops P) (λ h → Σ (Node P w h) (λ n → Node P (fst (κ h n)) g))
  subst-nd-to (lf i) κ g (lift ())
  subst-nd-to (nd (f , ϕ)) κ g n with
    graft-node-from P (fst (κ (_ , f) (inl idp)))
      (λ j l → subst (ϕ j (–> (snd (κ (_ , f) (inl idp)) j) l))
      (λ g n → κ g (inr (j , –> (snd (κ (_ , f) (inl idp)) j) l , n)))) g n
  subst-nd-to (nd (f , ϕ)) κ g n | inl n' = (_ , f) , inl idp , n'
  subst-nd-to (nd (f , ϕ)) κ g n | inr (k , l , n') = 
    let (w , α) = κ (_ , f) (inl idp)
        κ' j l g n = κ g (inr (j , –> (α j) l , n))
        ψ j l = subst (ϕ j (–> (α j) l)) (κ' j l)
        (h , n₀ , n₁) = subst-nd-to (ϕ k (–> (α k) l)) (κ' k l) g n'
    in h , (inr (k , –> (α k) l , n₀)) , n₁

  subst-nd-from : {i : I} (w : W P i)
    → (κ : (g : Ops P) → Node P w g → Op Subst g)
    → (g : Ops P) → Σ (Ops P) (λ h → Σ (Node P w h) (λ n → Node P (fst (κ h n)) g))
    → Node P (subst w κ) g
  subst-nd-from (lf i) κ g (h , lift () , n₁)
  subst-nd-from (nd (f , ϕ)) κ g (._ , inl idp , n₁) = 
    let (w , α) = κ (_ , f) (inl idp)
        κ' j l g n = κ g (inr (j , –> (α j) l , n))
        ψ j l = subst (ϕ j (–> (α j) l)) (κ' j l)
    in graft-node-to P w ψ g (inl n₁)
  subst-nd-from (nd (f , ϕ)) κ g (h , inr (k , p , n₀) , n₁) = 
    let (w , α) = κ (_ , f) (inl idp)
        κ' j l g n = κ g (inr (j , –> (α j) l , n))
        ψ j l = subst (ϕ j (–> (α j) l)) (κ' j l)
        n' = subst-nd-from (ϕ k p) (λ g n → κ g (inr (k , p , n))) g (h , n₀ , n₁)
        Q x = Node P (subst (ϕ k x) (λ g n → κ g (inr (k , x , n)))) g
    in graft-node-to P w ψ g (inr (k , <– (α k) p , transport! Q (<–-inv-r (α k) p) n'))

  postulate

    subst-nd-to-from : {i : I} (w : W P i)
      → (κ : (g : Ops P) → Node P w g → Op Subst g)
      → (g : Ops P) (n : Σ (Ops P) (λ h → Σ (Node P w h) (λ n → Node P (fst (κ h n)) g)))
      → subst-nd-to w κ g (subst-nd-from w κ g n) == n

    subst-nd-from-to : {i : I} (w : W P i)
      → (κ : (g : Ops P) → Node P w g → Op Subst g)
      → (g : Ops P) (n : Node P (subst w κ) g)
      → subst-nd-from w κ g (subst-nd-to w κ g n) == n

  subst-nd-eqv : {i : I} (w : W P i)
    → (κ : (g : Ops P) → Node P w g → Op Subst g)
    → (g : Ops P) → Node P (subst w κ) g ≃ Σ (Ops P) (λ h → Σ (Node P w h) (λ n → Node P (fst (κ h n)) g))
  subst-nd-eqv w κ g = equiv (subst-nd-to w κ g) (subst-nd-from w κ g)
    (subst-nd-to-from w κ g) (subst-nd-from-to w κ g)

  -- Iterated substitution (what was called flatten ...)
  μ-subst : {f : Ops P} → W Subst f → Op Subst f
  μ-subst {i , f} (lf .(i , f)) = corolla P f , corolla-lf-eqv P f
  μ-subst {i , f} (nd ((w , α) , κ)) =
    let κ' g n = μ-subst (κ g n)
    in subst w κ' , (λ j → α j ∘e (subst-lf-eqv w κ' j))

  -- Ah, the leaf frame is trivially part of what we did above.
  -- So we probably dont need this definition, but okay for now ...
  μ-subst-lf-eqv : {f : Ops P} (w : W Subst f)
    → (j : I) → Leaf P (fst (μ-subst w)) j ≃ Param P (snd f) j
  μ-subst-lf-eqv w j = snd (μ-subst w) j

  bd-frame-to : {f : Ops P} (pd : W Subst f)
    → (g : Ops P) → Leaf Subst pd g → Node P (fst (μ-subst pd)) g
  bd-frame-to (lf i) ._ idp = inl idp
  bd-frame-to (nd ((w , α) , κ)) g (h , n , l)=
    subst-nd-from w (λ g n → μ-subst (κ g n)) g
      (h , n , bd-frame-to (κ h n) g l)

  bd-frame-from : {f : Ops P} (pd : W Subst f)
    → (g : Ops P) → Node P (fst (μ-subst pd)) g → Leaf Subst pd g 
  bd-frame-from (lf i) .i (inl idp) = idp
  bd-frame-from (lf i) g (inr (j , p , ())) 
  bd-frame-from (nd ((w , α) , κ)) g n = 
    let (h , n₀ , n₁) = subst-nd-to w (λ g n → μ-subst (κ g n)) g n
    in h , n₀ , bd-frame-from (κ h n₀) g n₁
    
  postulate

    bd-frame-to-from : {f : Ops P} (pd : W Subst f)
      → (g : Ops P) (n : Node P (fst (μ-subst pd)) g)
      → bd-frame-to pd g (bd-frame-from pd g n) == n
      
    bd-frame-from-to : {f : Ops P} (pd : W Subst f)
      → (g : Ops P) (l : Leaf Subst pd g)
      → bd-frame-from pd g (bd-frame-to pd g l) == l

  μ-subst-frm : {f : Ops P} (pd : W Subst f)
    → Frame Subst pd (μ-subst pd)
  μ-subst-frm pd g = equiv (bd-frame-to pd g) (bd-frame-from pd g)
    (bd-frame-to-from pd g) (bd-frame-from-to pd g)

  --
  --  This guy's on deck!!
  --
  
  BD : Poly (Ops Subst)
  Op BD ((i , f) , (w , α)) = hfiber μ-subst (w , α)
  Param BD (pd , e) = Node Subst pd

  --   --
  --   --  Elimination Principles
  --   --

  --   flatten-lf-in : {i : I} {f : Op P i} (pd : W Q (i , f))
  --     → (j : I) → Param P f j → Leaf P (flatten pd) j 
  --   flatten-lf-in = flatten-frm-from 

  --   flatten-lf-elim : ∀ {ℓ'} {i : I} {f : Op P i}
  --     → (pd : W Q (i , f)) (j : I)
  --     → (Q : Leaf P (flatten pd) j → Type ℓ')
  --     → (σ : (p : Param P f j) → Q (flatten-lf-in pd j p))
  --     → (l : Leaf P (flatten pd) j) → Q l
  --   flatten-lf-elim pd j Q σ l = transport Q (<–-inv-l (flatten-frm pd j) l) (σ (flatten-frm-to pd j l))

  --   postulate

  --     flatten-lf-elim-β : ∀ {ℓ'} {i : I} {f : Op P i}
  --       → (pd : W Q (i , f)) (j : I)
  --       → (Q : Leaf P (flatten pd) j → Type ℓ')
  --       → (σ : (p : Param P f j) → Q (flatten-lf-in pd j p))
  --       → (p : Param P f j)
  --       → flatten-lf-elim pd j Q σ (flatten-lf-in pd j p) == σ p

  --   subst-lf-in : {i : I} (w : W P i)
  --     → (κ : (g : Ops P) → Node P w g → W Q g)
  --     → ∀ j → Leaf P w j → Leaf P (substitute w κ) j
  --   subst-lf-in = substitute-lf-from

  --   subst-lf-elim : ∀ {ℓ'} {i : I} (w : W P i)
  --     → (κ : (g : Ops P) → Node P w g → W Q g) (j : I)
  --     → (Q : Leaf P (substitute w κ) j → Type ℓ')
  --     → (σ : (l : Leaf P w j) → Q (subst-lf-in w κ j l))
  --     → (l : Leaf P (substitute w κ) j) → Q l
  --   subst-lf-elim w κ j Q σ l = transport Q (<–-inv-l (substitute-lf-eqv w κ j) l) (σ (substitute-lf-to w κ j l))

  --   postulate

  --     subst-lf-elim-β : ∀ {ℓ'} {i : I} (w : W P i)
  --       → (κ : (g : Ops P) → Node P w g → W Q g) (j : I)
  --       → (Q : Leaf P (substitute w κ) j → Type ℓ')
  --       → (σ : (l : Leaf P w j) → Q (subst-lf-in w κ j l))
  --       → (l : Leaf P w j)
  --       → subst-lf-elim w κ j Q σ (subst-lf-in w κ j l) == σ l


