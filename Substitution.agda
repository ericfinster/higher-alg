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
  subst-lf-to (nd (f , ϕ)) κ j = 
    let (w , α) = κ (_ , f) (inl idp)
        κ' j l g n = κ g (inr (j , –> (α j) l , n))
        ψ j l = subst (ϕ j (–> (α j) l)) (κ' j l)
    in graft-leaf-rec P w ψ j (λ k l₀ l₁ →
         k , –> (α k) l₀ , subst-lf-to (ϕ k (–> (α k) l₀)) (κ' k l₀) j l₁) 

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

  -- subst leaf elimination
  
  subst-lf-in : {i : I} (w : W P i)
    → (κ : (g : Ops P) → Node P w g → Op Subst g)
    → (j : I) → Leaf P w j → Leaf P (subst w κ) j
  subst-lf-in = subst-lf-from

  subst-lf-elim : {i : I} (w : W P i)
    → (κ : (g : Ops P) → Node P w g → Op Subst g) (j : I)
    → (Q : Leaf P (subst w κ) j → Type ℓ)
    → (σ : (l : Leaf P w j) → Q (subst-lf-in w κ j l))
    → (l : Leaf P (subst w κ) j) → Q l
  subst-lf-elim w κ j Q σ l =
    transport Q (<–-inv-l (subst-lf-eqv w κ j) l)
                (σ (subst-lf-to w κ j l))

  -- subst-lf-elim (lf i) κ j Q σ l = σ l
  -- subst-lf-elim (nd (f , ϕ)) κ j Q σ l = 
  --   let (w , α) = κ (_ , f) (inl idp)
  --       κ' j l g n = κ g (inr (j , –> (α j) l , n))
  --       ψ j l = subst (ϕ j (–> (α j) l)) (κ' j l)
  --   in graft-leaf-elim P w ψ j Q (λ k l₀ → subst-lf-elim (ϕ k (–> (α k) l₀)) (κ' k l₀) j
  --        (λ l₁ → Q (graft-leaf-to P w ψ j (k , l₀ , l₁)))
  --        (λ lϕ → transport (λ x → Q (graft-leaf-to P w ψ j x)) (pair= idp (pair= (<–-inv-l (α k) l₀) {!!}))
  --          (σ (k , (–> (α k) l₀) , lϕ)))) l

  postulate

    -- Should not be hard from the equivalence coherences ...
    subst-lf-elim-β : {i : I} (w : W P i)
      → (κ : (g : Ops P) → Node P w g → Op Subst g) (j : I)
      → (Q : Leaf P (subst w κ) j → Type ℓ)
      → (σ : (l : Leaf P w j) → Q (subst-lf-in w κ j l))
      → (l : Leaf P w j)
      → subst-lf-elim w κ j Q σ (subst-lf-in w κ j l) == σ l

  -- The recursor
  
  subst-lf-rec : {A : Type ℓ} {i : I} (w : W P i)
    → (κ : (g : Ops P) → Node P w g → Op Subst g) (j : I)
    → (σ : Leaf P w j → A)
    → Leaf P (subst w κ) j → A
  subst-lf-rec w κ j σ = σ ∘ (–> (subst-lf-eqv w κ j))

  subst-lf-rec-β : {A : Type ℓ} {i : I} (w : W P i)
    → (κ : (g : Ops P) → Node P w g → Op Subst g) (j : I)
    → (σ : Leaf P w j → A)
    → (l : Leaf P w j)
    → subst-lf-rec w κ j σ (subst-lf-in w κ j l) == σ l
  subst-lf-rec-β w κ j σ l = ap σ (<–-inv-r (subst-lf-eqv w κ j) l)


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

  -- subst node elim

  subst-nd-in : {i : I} (w : W P i)
    → (κ : (g : Ops P) → Node P w g → Op Subst g)
    → (g : Ops P) (h : Ops P) (n₀ : Node P w h) (n₁ : Node P (fst (κ h n₀)) g)
    → Node P (subst w κ) g
  subst-nd-in w κ g h n₀ n₁ = subst-nd-from w κ g (h , n₀ , n₁)

  subst-nd-elim : {i : I} (w : W P i)
    → (κ : (g : Ops P) → Node P w g → Op Subst g) (g : Ops P)
    → (Q : Node P (subst w κ) g → Type ℓ)
    → (σ : (h : Ops P) (n₀ : Node P w h) (n₁ : Node P (fst (κ h n₀)) g)
           → Q (subst-nd-in w κ g h n₀ n₁))
    → (n : Node P (subst w κ) g) → Q n
  subst-nd-elim w κ g Q σ n = 
    let (h , n₀ , n₁) = subst-nd-to w κ g n
    in transport Q (<–-inv-l (subst-nd-eqv w κ g) n) (σ h n₀ n₁)

  postulate
  
    subst-nd-elim-β : {i : I} (w : W P i)
      → (κ : (g : Ops P) → Node P w g → Op Subst g) (g : Ops P)
      → (Q : Node P (subst w κ) g → Type ℓ)
      → (σ : (h : Ops P) (n₀ : Node P w h) (n₁ : Node P (fst (κ h n₀)) g)
             → Q (subst-nd-in w κ g h n₀ n₁))
      → (h : Ops P) (n₀ : Node P w h) (n₁ : Node P (fst (κ h n₀)) g)
      → subst-nd-elim w κ g Q σ (subst-nd-in w κ g h n₀ n₁) == σ h n₀ n₁

  -- subst recursor

  subst-nd-rec : {A : Type ℓ} {i : I} (w : W P i)
    → (κ : (g : Ops P) → Node P w g → Op Subst g) (g : Ops P)
    → (σ : Σ (Ops P) (λ h → Σ (Node P w h) (λ n → Node P (fst (κ h n)) g)) → A)
    → Node P (subst w κ) g → A
  subst-nd-rec w κ g σ n = σ (subst-nd-to w κ g n)

  -- Substitution monad structure 

  -- Here we split flatten and its frame into two pieces.
  -- We will have to see what ends up being the most convenient...
  flatn : {i : I} {f : Op P i} → W Subst (i , f) → W P i
  flatn-frm : {i : I} {f : Op P i} (w : W Subst (i , f)) → Frame P (flatn w) f
  
  flatn (lf (i , f)) = corolla P f
  flatn (nd ((w , α) , κ)) = subst w (λ g n → flatn (κ g n) , flatn-frm (κ g n))
    
  flatn-frm (lf (i , f)) = corolla-frm P f
  flatn-frm (nd ((w , α) , κ)) j = α j ∘e
    subst-lf-eqv w (λ g n → flatn (κ g n) , flatn-frm (κ g n)) j

  -- Iterated substitution (what was called flatten ...)
  μ-subst : {f : Ops P} → W Subst f → Op Subst f
  μ-subst pd = flatn pd , flatn-frm pd

  bd-frame-to : {f : Ops P} (pd : W Subst f)
    → (g : Ops P) → Leaf Subst pd g → Node P (flatn pd) g
  bd-frame-to (lf i) ._ idp = inl idp
  bd-frame-to (nd ((w , α) , κ)) g (h , n , l)=
    subst-nd-from w (λ g n → μ-subst (κ g n)) g
      (h , n , bd-frame-to (κ h n) g l)

  bd-frame-from : {f : Ops P} (pd : W Subst f)
    → (g : Ops P) → Node P (flatn pd) g → Leaf Subst pd g 
  bd-frame-from (lf i) .i (inl idp) = idp
  bd-frame-from (lf i) g (inr (j , p , ())) 
  bd-frame-from (nd ((w , α) , κ)) g n = 
    let (h , n₀ , n₁) = subst-nd-to w (λ g n → μ-subst (κ g n)) g n
    in h , n₀ , bd-frame-from (κ h n₀) g n₁
    
  postulate

    bd-frame-to-from : {f : Ops P} (pd : W Subst f)
      → (g : Ops P) (n : Node P (flatn pd) g)
      → bd-frame-to pd g (bd-frame-from pd g n) == n
      
    bd-frame-from-to : {f : Ops P} (pd : W Subst f)
      → (g : Ops P) (l : Leaf Subst pd g)
      → bd-frame-from pd g (bd-frame-to pd g l) == l

  bd-frm : {f : Ops P} (pd : W Subst f)
    → Frame Subst pd (μ-subst pd)
  bd-frm pd g = equiv (bd-frame-to pd g) (bd-frame-from pd g)
    (bd-frame-to-from pd g) (bd-frame-from-to pd g)

  subst-mgm : PolyMagma Subst
  PolyMagma.μ subst-mgm w = flatn w , flatn-frm w
  PolyMagma.μ-frm subst-mgm w = bd-frm w
