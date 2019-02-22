{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Grafting

module Substitution {ℓ} {I : Type ℓ} (P : Poly I) where

  -- Elementary substitution.
  subst : {i : I} (w : W P i)
    → (κ : (g : Ops P) → Node P w g → InFrame P g)
    → W P i
  subst (lf i) κ = lf i
  subst (nd (f , ϕ)) κ =
    let (w , α) = κ (_ , f) (inl idp)
        κ' j l g n = κ g (inr (j , –> (α j) l , n))
        ψ j l = subst (ϕ j (–> (α j) l)) (κ' j l)
    in graft P w ψ

  -- Leaves in a substitution
  subst-leaf-to : {i : I} (w : W P i)
    → (κ : (g : Ops P) → Node P w g → InFrame P g)
    → (j : I) → Leaf P w j → Leaf P (subst w κ) j 
  subst-leaf-to (lf i) κ j l = l
  subst-leaf-to (nd (f , ϕ)) κ j (k , p , l) = 
    let (w , α) = κ (_ , f) (inl idp)
        κ' j l g n = κ g (inr (j , –> (α j) l , n))
        ψ j l = subst (ϕ j (–> (α j) l)) (κ' j l)
        l' = subst-leaf-to (ϕ k p) (λ g n → κ g (inr (k , p , n))) j l
        Q x = Leaf P (subst (ϕ k x) (λ g n → κ g (inr (k , x , n)))) j
    in graft-leaf-to P w ψ j (k , <– (α k) p , transport! Q (<–-inv-r (α k) p) l')

  subst-leaf-from : {i : I} (w : W P i)
    → (κ : (g : Ops P) → Node P w g → InFrame P g)
    → (j : I) → Leaf P (subst w κ) j → Leaf P w j
  subst-leaf-from (lf i) κ j l = l
  subst-leaf-from (nd (f , ϕ)) κ j l = 
    let (w , α) = κ (_ , f) (inl idp)
        κ' j l g n = κ g (inr (j , –> (α j) l , n))
        ψ j l = subst (ϕ j (–> (α j) l)) (κ' j l)
        (k , l₀ , l₁) = graft-leaf-from P w ψ j l
    in k , –> (α k) l₀ , subst-leaf-from (ϕ k (–> (α k) l₀)) (κ' k l₀) j l₁

  subst-leaf-to-from : {i : I} (w : W P i)
    → (κ : (g : Ops P) → Node P w g → InFrame P g)
    → (j : I) (l : Leaf P (subst w κ) j)
    → subst-leaf-to w κ j (subst-leaf-from w κ j l) == l
  subst-leaf-to-from (lf i) κ j l = idp
  subst-leaf-to-from (nd (f , ϕ)) κ j l = 
    let (w , α) = κ (_ , f) (inl idp)
        κ' j l g n = κ g (inr (j , –> (α j) l , n))
        ψ j l = subst (ϕ j (–> (α j) l)) (κ' j l)
        (k , l₀ , l₁) = graft-leaf-from P w ψ j l
        p = –> (α k) l₀
        Q x = Leaf P (subst (ϕ k x) (λ g n → κ g (inr (k , x , n)))) j
        l' = subst-leaf-to (ϕ k p) (κ' k l₀) j
               (subst-leaf-from (ϕ k p) (κ' k l₀) j l₁)
               
    in graft-leaf-to P w ψ j (k , <– (α k) p , transport! Q (<–-inv-r (α k) p) l')
         =⟨ subst-leaf-to-from (ϕ k p) (κ' k l₀) j l₁
              |in-ctx (λ x → graft-leaf-to P w ψ j (k , <– (α k) p , transport! Q (<–-inv-r (α k) p) x)) ⟩
       graft-leaf-to P w ψ j (k , <– (α k) p , transport! Q (<–-inv-r (α k) p) l₁)
         =⟨ pair= (<–-inv-l (α k) l₀) (transp!-eqv-lem {C = Q} (α k) l₀ l₁)
              |in-ctx (λ x → graft-leaf-to P w ψ j (k , x)) ⟩
       graft-leaf-to P w ψ j (k , l₀ , l₁)
         =⟨ graft-leaf-to-from P w ψ j l ⟩ 
       l ∎

  -- Ech.  Not very pretty.  And why is it so much longer than
  -- the previous one?
  subst-leaf-from-to : {i : I} (w : W P i)
    → (κ : (g : Ops P) → Node P w g → InFrame P g)
    → (j : I) (l : Leaf P w j)
    → subst-leaf-from w κ j (subst-leaf-to w κ j l) == l
  subst-leaf-from-to (lf i) κ .i idp = idp
  subst-leaf-from-to (nd (f , ϕ)) κ j (k , p , l) =
    let (w , α) = κ (_ , f) (inl idp)
        κ' j l g n = κ g (inr (j , –> (α j) l , n))
        ψ j l = subst (ϕ j (–> (α j) l)) (κ' j l)
        l' = subst-leaf-to (ϕ k p) (λ g n → κ g (inr (k , p , n))) j l
        Q x = Leaf P (subst (ϕ k x) (λ g n → κ g (inr (k , x , n)))) j
        (k₀ , l₀ , l₁) = graft-leaf-from P w ψ j (graft-leaf-to P w ψ j (k , <– (α k) p , transport! Q (<–-inv-r (α k) p) l'))
        p' = –> (α k) (<– (α k) p)
    in k₀ , –> (α k₀) l₀ , subst-leaf-from (ϕ k₀ (–> (α k₀) l₀)) (κ' k₀ l₀) j l₁
         =⟨ ap (λ x → let (a , b , c) = x in a , –> (α a) b , subst-leaf-from (ϕ a (–> (α a) b)) (κ' a b) j c)
             (graft-leaf-from-to P w ψ j (k , <– (α k) p , transport! Q (<–-inv-r (α k) p) l')) ⟩
       k , p' , subst-leaf-from (ϕ k p') (κ' k (<– (α k) p)) j (transport! Q (<–-inv-r (α k) p) l')
         =⟨ ! (transp!-→ (λ x → Leaf P (ϕ k x) j) Q (<–-inv-r (α k) p) (λ pₓ lₓ → subst-leaf-to (ϕ k pₓ) (λ g n → κ g (inr (k , pₓ , n))) j lₓ))
              |in-ctx (λ x → k , p' , subst-leaf-from (ϕ k p') (κ' k (<– (α k) p)) j x) ⟩
       k , p' , subst-leaf-from (ϕ k p') (κ' k (<– (α k) p)) j
                  (subst-leaf-to (ϕ k p') (κ' k (<– (α k) p)) j
                    (transport! (λ x → Leaf P (ϕ k x) j) (<–-inv-r (α k) p) l))
         =⟨ subst-leaf-from-to (ϕ k p') (κ' k (<– (α k) p)) j
              (transport! (λ x → Leaf P (ϕ k x) j) (<–-inv-r (α k) p) l)
             |in-ctx (λ x → k , p' , x) ⟩ 
       k , p' , transport! (λ x → Leaf P (ϕ k x) j) (<–-inv-r (α k) p) l
         =⟨ pair= idp (pair= (<–-inv-r (α k) p) (to-transp!!-↓ (λ x → Leaf P (ϕ k x) j) (<–-inv-r (α k) p) l)) ⟩ 
       k , p , l ∎

  subst-leaf-eqv : {i : I} (w : W P i)
    → (κ : (g : Ops P) → Node P w g → InFrame P g)
    → (j : I) → Leaf P w j ≃ Leaf P (subst w κ) j 
  subst-leaf-eqv w κ j = equiv (subst-leaf-to w κ j) (subst-leaf-from w κ j)
    (subst-leaf-to-from w κ j) (subst-leaf-from-to w κ j)

  -- Nodes in a substitution
  subst-node-to : {i : I} (w : W P i)
    → (κ : (g : Ops P) → Node P w g → InFrame P g)
    → (g : Ops P) → Σ (Ops P) (λ h → Σ (Node P w h) (λ n → Node P (fst (κ h n)) g))
    → Node P (subst w κ) g
  subst-node-to (lf i) κ g (h , lift () , n₁)
  subst-node-to (nd (f , ϕ)) κ g (._ , inl idp , n₁) = 
    let (w , α) = κ (_ , f) (inl idp)
        κ' j l g n = κ g (inr (j , –> (α j) l , n))
        ψ j l = subst (ϕ j (–> (α j) l)) (κ' j l)
    in graft-node-to P w ψ g (inl n₁)
  subst-node-to (nd (f , ϕ)) κ g (h , inr (k , p , n₀) , n₁) = 
    let (w , α) = κ (_ , f) (inl idp)
        κ' j l g n = κ g (inr (j , –> (α j) l , n))
        ψ j l = subst (ϕ j (–> (α j) l)) (κ' j l)
        n' = subst-node-to (ϕ k p) (λ g n → κ g (inr (k , p , n))) g (h , n₀ , n₁)
        Q x = Node P (subst (ϕ k x) (λ g n → κ g (inr (k , x , n)))) g
    in graft-node-to P w ψ g (inr (k , <– (α k) p , transport! Q (<–-inv-r (α k) p) n'))

  subst-node-from : {i : I} (w : W P i)
    → (κ : (g : Ops P) → Node P w g → InFrame P g)
    → (g : Ops P) → Node P (subst w κ) g
    → Σ (Ops P) (λ h → Σ (Node P w h) (λ n → Node P (fst (κ h n)) g))

  subst-node-from-lcl : {i : I} (f : Op P i)
    → (ϕ : (j : I) → Param P f j → W P j) 
    → (κ : (h : Ops P) → Node P (nd (f , ϕ)) h → InFrame P h) (g : Ops P)
    → (n : let (w , α) = κ (_ , f) (inl idp)
               κ' j l h n = κ h (inr (j , –> (α j) l , n))
               ψ j l = subst (ϕ j (–> (α j) l)) (κ' j l)
           in Node P w g ⊔ Σ I (λ j → Σ (Leaf P w j) (λ l → Node P (ψ j l) g)))
    → Σ (Ops P) (λ h → Σ (Node P (nd (f , ϕ)) h) (λ n' → Node P (fst (κ h n')) g))

  subst-node-from (lf i) κ g (lift ())
  subst-node-from (nd (f , ϕ)) κ g n = 
    let (w , α) = κ (_ , f) (inl idp)
        κ' j l g n = κ g (inr (j , –> (α j) l , n))
        ψ j l = subst (ϕ j (–> (α j) l)) (κ' j l)
    in  subst-node-from-lcl f ϕ κ g (graft-node-from P w ψ g n) 

  subst-node-from-lcl f ϕ κ g =
    ⊔-rec (λ n → (_ , f) , inl idp , n)
          (λ t → let (j , l , n) = t
                     (w , α) = κ (_ , f) (inl idp)
                     κ' j l g n = κ g (inr (j , –> (α j) l , n))
                     ψ j l = subst (ϕ j (–> (α j) l)) (κ' j l)
                     (h , n₀ , n₁) = subst-node-from (ϕ j (–> (α j) l)) (κ' j l) g n
                  in h , inr (j , –> (α j) l , n₀) , n₁)

  postulate

    subst-node-to-from : {i : I} (w : W P i)
      → (κ : (g : Ops P) → Node P w g → InFrame P g)
      → (g : Ops P) (n : Node P (subst w κ) g)
      → subst-node-to w κ g (subst-node-from w κ g n) == n
      
    subst-node-from-to : {i : I} (w : W P i)
      → (κ : (g : Ops P) → Node P w g → InFrame P g)
      → (g : Ops P) (n : Σ (Ops P) (λ h → Σ (Node P w h) (λ n → Node P (fst (κ h n)) g)))
      → subst-node-from w κ g (subst-node-to w κ g n) == n

  subst-node-eqv : {i : I} (w : W P i)
    → (κ : (g : Ops P) → Node P w g → InFrame P g) (g : Ops P)
    → Σ (Ops P) (λ h → Σ (Node P w h) (λ n → Node P (fst (κ h n)) g))
    ≃ Node P (subst w κ) g 
  subst-node-eqv w κ g = equiv (subst-node-to w κ g) (subst-node-from w κ g)
    (subst-node-to-from w κ g) (subst-node-from-to w κ g)


  --
  --  Abbreviations with implicit arguments
  --

  subst-lf-to : {i : I} {w : W P i}
    → {κ : (g : Ops P) → Node P w g → InFrame P g}
    → {j : I} → Leaf P w j → Leaf P (subst w κ) j 
  subst-lf-to {i} {w} {κ} {j} = subst-leaf-to w κ j

  subst-lf-from : {i : I} {w : W P i}
    → {κ : (g : Ops P) → Node P w g → InFrame P g}
    → {j : I} → Leaf P (subst w κ) j → Leaf P w j
  subst-lf-from {i} {w} {κ} {j} = subst-leaf-from w κ j

  subst-lf-to-from : {i : I} {w : W P i}
    → {κ : (g : Ops P) → Node P w g → InFrame P g}
    → {j : I} (l : Leaf P (subst w κ) j)
    → subst-leaf-to w κ j (subst-leaf-from w κ j l) == l
  subst-lf-to-from {i} {w} {κ} {j} =
    subst-leaf-to-from w κ j
    
  subst-lf-from-to : {i : I} {w : W P i}
    → {κ : (g : Ops P) → Node P w g → InFrame P g}
    → {j : I} (l : Leaf P w j)
    → subst-leaf-from w κ j (subst-leaf-to w κ j l) == l
  subst-lf-from-to {i} {w} {κ} {j} =
    subst-leaf-from-to w κ j

  subst-nd-to : {i : I} {w : W P i}
    → {κ : (g : Ops P) → Node P w g → InFrame P g}
    → {g : Ops P} → Σ (Ops P) (λ h → Σ (Node P w h) (λ n → Node P (fst (κ h n)) g))
    → Node P (subst w κ) g
  subst-nd-to {i} {w} {κ} {g} = subst-node-to w κ g
  
  subst-nd-from : {i : I} {w : W P i}
    → {κ : (g : Ops P) → Node P w g → InFrame P g}
    → {g : Ops P} → Node P (subst w κ) g
    → Σ (Ops P) (λ h → Σ (Node P w h) (λ n → Node P (fst (κ h n)) g))
  subst-nd-from {i} {w} {κ} {g} = subst-node-from w κ g

