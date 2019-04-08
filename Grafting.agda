{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial

module Grafting {ℓ} {I : Type ℓ} (P : Poly I) where

  module GraftLocal {i : I} (f : Op P i)
    (ϕ : Decor P f (W P)) (ψ : Decor (Fr P) (nd (f , ϕ)) (W P)) where
    
    ψg : (j : I) (p : Param P f j) → Decor (Fr P) (ϕ j p) (W P)
    ψg j p k l = ψ k (j , p , l)

  graft : {i : I} (w : W P i) (ψ : Decor (Fr P) w (W P)) → W P i
  graft (lf i) ψ = ψ i idp
  graft (nd (f ,  ϕ)) ψ = 
    let open GraftLocal f ϕ ψ 
        ϕ' j p = graft (ϕ j p) (ψg j p)
    in nd (f ,  ϕ')

  --
  --  Leaves in a graft
  --

  graft-leaf-to : {i : I} (w : W P i) (ψ : Decor (Fr P) w (W P)) (k : I)
    → Σ I (λ j → Σ (Leaf P w j) (λ l → Leaf P (ψ j l) k))
    → Leaf P (graft w ψ) k
  graft-leaf-to (lf i) ψ k (.i , idp , l) = l
  graft-leaf-to (nd (f ,  ϕ)) ψ k (j₁ , (j₀ , p , l₀) , l₁) = 
    let open GraftLocal f ϕ ψ 
    in (j₀ , p , graft-leaf-to (ϕ j₀ p) (ψg j₀ p) k (j₁ , l₀ , l₁))

  graft-leaf-from : {i : I} (w : W P i) (ψ : Decor (Fr P) w (W P)) (k : I)
    → Leaf P (graft w ψ) k
    → Σ I (λ j → Σ (Leaf P w j) (λ l → Leaf P (ψ j l) k))
  graft-leaf-from (lf i) ψ k l = i , idp , l
  graft-leaf-from (nd (f ,  ϕ)) ψ k (j , p , l) = 
    let open GraftLocal f ϕ ψ
        (s , t , u) = graft-leaf-from (ϕ j p) (ψg j p) k l
    in s , (j , p , t) , u

  graft-leaf-to-from : {i : I} (w : W P i) (ψ : Decor (Fr P) w (W P))
    → (k : I) (l : Leaf P (graft w ψ) k)
    → graft-leaf-to w ψ k (graft-leaf-from w ψ k l) == l
  graft-leaf-to-from (lf i) ψ k l = idp
  graft-leaf-to-from (nd (f ,  ϕ)) ψ k (j , p , l) =
    let open GraftLocal f ϕ ψ 
    in ap (λ x → (j , p , x)) (graft-leaf-to-from (ϕ j p) (ψg j p) k l) 

  graft-leaf-from-to : {i : I} (w : W P i) (ψ : Decor (Fr P) w (W P)) (k : I)
    → (l : Σ I (λ j → Σ (Leaf P w j) (λ l → Leaf P (ψ j l) k)))
    → graft-leaf-from w ψ k (graft-leaf-to w ψ k l) == l
  graft-leaf-from-to (lf i) ψ k (.i , idp , l₁) = idp
  graft-leaf-from-to (nd (f ,  ϕ)) ψ k (j₁ , (j₀ , p , l₀) , l₁) =
    let open GraftLocal f ϕ ψ 
        ih = graft-leaf-from-to (ϕ j₀ p) (ψg j₀ p) k (j₁ , l₀ , l₁)
    in ap (λ x → (fst x , (j₀ , p , fst (snd x)) , snd (snd x))) ih

  graft-leaf-eqv : {i : I} (w : W P i) (ψ : Decor (Fr P) w (W P)) (k : I)
    → Σ I (λ j → Σ (Leaf P w j) (λ l → Leaf P (ψ j l) k)) ≃ Leaf P (graft w ψ) k
  graft-leaf-eqv w ψ k =
    equiv (graft-leaf-to w ψ k) (graft-leaf-from w ψ k)
          (graft-leaf-to-from w ψ k) (graft-leaf-from-to w ψ k)

  -- Implicit versions
  graft-lf-to : {i : I} {w : W P i}
    → {ψ : Decor (Fr P) w (W P)} {k : I}
    → Σ I (λ j → Σ (Leaf P w j) (λ l → Leaf P (ψ j l) k))
    → Leaf P (graft w ψ) k
  graft-lf-to {i} {w} {ψ} {k} = graft-leaf-to w ψ k
  
  graft-lf-from : {i : I} {w : W P i}
    → {ψ : Decor (Fr P) w (W P)} {k : I}
    → Leaf P (graft w ψ) k
    → Σ I (λ j → Σ (Leaf P w j) (λ l → Leaf P (ψ j l) k))
  graft-lf-from {i} {w} {ψ} {k} = graft-leaf-from w ψ k

  --
  --  Nodes in a graft
  --

  graft-node-to : {i : I} (w : W P i)
    → (ψ : Decor (Fr P) w (W P)) (g : Ops P)
    → Node P w g ⊔ Σ I (λ k → Σ (Leaf P w k) (λ l → Node P (ψ k l) g))
    → Node P (graft w ψ) g
  graft-node-to (lf i) ψ g (inl ())
  graft-node-to (lf i) ψ g (inr (.i , idp , n)) = n
  graft-node-to (nd (f ,  ϕ)) ψ ._ (inl (inl idp)) = inl idp
  graft-node-to (nd (f ,  ϕ)) ψ g (inl (inr (j , p , n))) =
    inr (j , p , graft-node-to (ϕ j p) (λ k l → ψ k (j , p , l)) g (inl n))
  graft-node-to (nd (f ,  ϕ)) ψ g (inr (k , (j , p , l) , n)) = 
    inr (j , p , graft-node-to (ϕ j p) (λ k l → ψ k (j , p , l)) g (inr (k , l , n)))

  graft-node-from : {i : I} (w : W P i)
    → (ψ : Decor (Fr P) w (W P)) (g : Ops P)
    → Node P (graft w ψ) g
    → Node P w g ⊔ Σ I (λ k → Σ (Leaf P w k) (λ l → Node P (ψ k l) g))

  graft-node-from-lcl : {i : I} (f : Op P i)
    → (ϕ : ∀ j → Param P f j → W P j)
    → (ψ : ∀ j → Leaf P (nd (f , ϕ)) j → W P j)
    → (g : Ops P) (j : I) (p : Param P f j)
    → (n : Node P (ϕ j p) g ⊔ Σ I (λ k → Σ (Leaf P (ϕ j p) k) (λ l → Node P (ψ k (j , p , l)) g)))
    → Node P (nd (f , ϕ)) g ⊔ Σ I (λ k → Σ (Leaf P (nd (f , ϕ)) k) (λ l → Node P (ψ k l) g))

  graft-node-from (lf i) ψ g n = inr (i , idp , n)
  graft-node-from (nd (f ,  ϕ)) ψ ._ (inl idp) = inl (inl idp)
  graft-node-from (nd (f ,  ϕ)) ψ g (inr (j , p , n)) =
    graft-node-from-lcl f ϕ ψ g j p
      (graft-node-from (ϕ j p) (λ k l → ψ k (j , p , l)) g n)

  graft-node-from-lcl f ϕ ψ g j p =
    ⊔-rec (λ n → inl (inr (j , p , n)))
          (λ t → let (k , l , n) = t in inr ((k , (j , p , l) , n)))

  graft-node-to-from : {i : I} (w : W P i)
    → (ψ : Decor (Fr P) w (W P)) (g : Ops P)
    → (n : Node P (graft w ψ) g)
    → graft-node-to w ψ g (graft-node-from w ψ g n) == n

  graft-node-to-from-lcl : {i : I} (f : Op P i)
    → (ϕ : ∀ j → Param P f j → W P j)
    → (ψ : ∀ j → Leaf P (nd (f , ϕ)) j → W P j)
    → (g : Ops P) (j : I) (p : Param P f j)
    → (n : Node P (ϕ j p) g ⊔ Σ I (λ k → Σ (Leaf P (ϕ j p) k) (λ l → Node P (ψ k (j , p , l)) g)))
    → graft-node-to (nd (f , ϕ)) ψ g (graft-node-from-lcl f ϕ ψ g j p n)
      == inr (j , p , graft-node-to (ϕ j p) (λ k l → ψ k (j , p , l)) g n)

  graft-node-to-from (lf i) ψ g n = idp
  graft-node-to-from (nd (f ,  ϕ)) ψ ._ (inl idp) = idp
  graft-node-to-from (nd (f ,  ϕ)) ψ g (inr (j , p , n)) =
    graft-node-to-from-lcl f ϕ ψ g j p
      (graft-node-from (ϕ j p) (λ k l → ψ k (j , p , l)) g n) ∙
    ap (λ x → inr (j , p , x)) (graft-node-to-from (ϕ j p) (λ k l → ψ k (j , p , l)) g n)

  graft-node-to-from-lcl f ϕ ψ g j p (inl n) = idp
  graft-node-to-from-lcl f ϕ ψ g j p (inr (k , l , n)) = idp

  graft-node-from-to : {i : I} (w : W P i)
    → (ψ : Decor (Fr P) w (W P)) (g : Ops P)
    → (n : Node P w g ⊔ Σ I (λ k → Σ (Leaf P w k) (λ l → Node P (ψ k l) g)))
    → graft-node-from w ψ g (graft-node-to w ψ g n) == n
  graft-node-from-to (lf i) ψ g (inl ())
  graft-node-from-to (lf i) ψ g (inr (.i , idp , n)) = idp
  graft-node-from-to (nd (f ,  ϕ)) ψ ._ (inl (inl idp)) = idp
  graft-node-from-to (nd (f ,  ϕ)) ψ g (inl (inr (j , p , n))) = 
    ap (graft-node-from-lcl f ϕ ψ g j p)
       (graft-node-from-to (ϕ j p) (λ k l → ψ k (j , p , l)) g (inl n))
  graft-node-from-to (nd (f ,  ϕ)) ψ g (inr (k , (j , p , l) , n)) =
    ap (graft-node-from-lcl f ϕ ψ g j p)
       (graft-node-from-to (ϕ j p) (λ k l → ψ k (j , p , l)) g (inr (k , l , n)))

  graft-node-eqv : {i : I} (w : W P i)
    → (ψ : Decor (Fr P) w (W P))
    → (g : Ops P)
    → Node P w g ⊔ Σ I (λ k → Σ (Leaf P w k) (λ l → Node P (ψ k l) g))
      ≃ Node P (graft w ψ) g
  graft-node-eqv w ψ g =
    equiv (graft-node-to w ψ g) (graft-node-from w ψ g)
          (graft-node-to-from w ψ g) (graft-node-from-to w ψ g)

  graft-nd-to : {i : I} {w : W P i}
    → {ψ : Decor (Fr P) w (W P)} {g : Ops P}
    → Node P w g ⊔ Σ I (λ k → Σ (Leaf P w k) (λ l → Node P (ψ k l) g))
    → Node P (graft w ψ) g
  graft-nd-to {i} {w} {ψ} {g} =
    graft-node-to w ψ g

  graft-nd-from : {i : I} {w : W P i}
    → {ψ : Decor (Fr P) w (W P)} {g : Ops P}
    → Node P (graft w ψ) g
    → Node P w g ⊔ Σ I (λ k → Σ (Leaf P w k) (λ l → Node P (ψ k l) g))
  graft-nd-from {i} {w} {ψ} {g} =
    graft-node-from w ψ g

  graft-nd-to-from : {i : I} {w : W P i}
    → {ψ : Decor (Fr P) w (W P)} {g : Ops P}
    → (n : Node P (graft w ψ) g)
    → graft-node-to w ψ g (graft-node-from w ψ g n) == n
  graft-nd-to-from {i} {w} {ψ} {g} =
    graft-node-to-from w ψ g
  
  graft-nd-from-to : {i : I} {w : W P i}
    → {ψ : Decor (Fr P) w (W P)} {g : Ops P}
    → (n : Node P w g ⊔ Σ I (λ k → Σ (Leaf P w k) (λ l → Node P (ψ k l) g)))
    → graft-node-from w ψ g (graft-node-to w ψ g n) == n
  graft-nd-from-to {i} {w} {ψ} {g} =
    graft-node-from-to w ψ g

  --
  -- Basic laws of grafting
  --

  -- grafting is unital
  graft-unit : {i : I} (w : W P i) → w == graft w (λ j l → lf j) 
  graft-unit (lf i) = idp
  graft-unit (nd (f , ϕ)) =
    ap (λ x → nd (f , x))
       (Decor-== P (λ j p → graft-unit (ϕ j p)))

  graft-unit-lf-to : {i : I} (w : W P i) (j : I)
    → Leaf P (graft w (λ k _ → lf k)) j
    → Leaf P w j
  graft-unit-lf-to (lf i) j l = l
  graft-unit-lf-to (nd (f , ϕ)) j (k , p , l) =
    k , p , graft-unit-lf-to (ϕ k p) j l

  graft-unit-lf-from : {i : I} (w : W P i) (j : I)
    → Leaf P w j
    → Leaf P (graft w (λ k _ → lf k)) j
  graft-unit-lf-from (lf i) j l = l
  graft-unit-lf-from (nd (f , ϕ)) j (k , p , l) =
    k , p , graft-unit-lf-from (ϕ k p) j l

  graft-unit-lf-to-from : {i : I} (w : W P i) (j : I)
    → (l : Leaf P w j)
    → graft-unit-lf-to w j (graft-unit-lf-from w j l) == l
  graft-unit-lf-to-from (lf i) j l = idp
  graft-unit-lf-to-from (nd (f , ϕ)) j (k , p , l) =
    ap (λ x → (k , p , x)) (graft-unit-lf-to-from (ϕ k p) j l)

  graft-unit-lf-from-to : {i : I} (w : W P i) (j : I)
    → (l : Leaf P (graft w (λ k _ → lf k)) j)
    → graft-unit-lf-from w j (graft-unit-lf-to w j l) == l
  graft-unit-lf-from-to (lf i) j l = idp
  graft-unit-lf-from-to (nd (f , ϕ)) j (k , p , l) =
    ap (λ x → (k , p , x)) (graft-unit-lf-from-to (ϕ k p) j l)

  graft-unit-lf-eqv : {i : I} (w : W P i) (j : I)
    → Leaf P (graft w (λ k _ → lf k)) j
    ≃ Leaf P w j
  graft-unit-lf-eqv w j =
    equiv (graft-unit-lf-to w j) (graft-unit-lf-from w j)
          (graft-unit-lf-to-from w j) (graft-unit-lf-from-to w j)

  graft-unit-lem : {i : I} (w : W P i)
    → (j : I) (l : Leaf P (graft w (λ j l → lf j)) j)
    → graft-unit-lf-to w j l == l [ (λ x → Leaf P x j) ↓ graft-unit w ]
  graft-unit-lem (lf i) j idp = idp
  graft-unit-lem (nd (f , ϕ)) j (k , p , l) = 
    ↓-ap-in (λ x → Leaf P x j) (λ x → nd (f , x)) 
            (↓-nd-Leaf-ih P (λ j p → graft-unit (ϕ j p)) k p
                            (graft-unit-lem (ϕ k p) j l))

  graft-unit-frm : {i : I} {f : Op P i}
    → (w : W P i) (α : Frame P w f)
    → α == (λ j → α j ∘e graft-unit-lf-eqv w j) [ (λ x → Frame P x f) ↓ graft-unit w ]
  graft-unit-frm w α =
    let lem j l₀ l₁ q = –> (α j) l₀
                          =⟨ to-transp! q |in-ctx (–> (α j)) ⟩
                        –> (α j) (transport! (λ x → Leaf P x j) (graft-unit w) l₁)
                          =⟨ ! (to-transp! (graft-unit-lem w j l₁)) |in-ctx (–> (α j)) ⟩
                        –> (α j) (graft-unit-lf-to w j l₁) ∎ 
    in ↓-W-Frame-in P lem

  graft-unit-nd : {i : I} (w : W P i)
    → (g : Ops P) (n : Node P w g)
    → n == graft-node-to w (λ j _ → lf j) g (inl n)
        [ (λ x → Node P x g) ↓ graft-unit w ]
  graft-unit-nd (lf i) g (lift ())
  graft-unit-nd (nd (f , ϕ)) .(_ , f) (inl idp) =
    ↓-ap-in (λ x → Node P x (_ , f)) (λ x → nd (f , x))
      (↓-Node-here-in P (Decor-== P (λ j p → graft-unit (ϕ j p))))
  graft-unit-nd (nd (f , ϕ)) g (inr (k , p , n)) = 
    ↓-ap-in (λ x → Node P x g) (λ x → nd (f , x))
      (↓-Node-there-in P (λ j p → graft-unit (ϕ j p)) k p
        (graft-unit-nd (ϕ k p) g n))

  -- Decoration for graft associativity
  GADecor : {i : I} (w : W P i)
    → (ψ₀ : Decor (Fr P) w (W P))
    → Type ℓ
  GADecor w ψ₀ = (k : I)
    → (t : Σ I (λ j → Σ (Leaf P w j) (λ l → Leaf P (ψ₀ j l) k)))
    → W P k

  -- graft associativity decorations
  graft-assoc-decor-left : {i : I} (w : W P i)
    → (ψ₀ : Decor (Fr P) w (W P)) (ψ₁ : GADecor w ψ₀)
    → Decor (Fr P) (graft w ψ₀) (W P)
  graft-assoc-decor-left w ψ₀ ψ₁ j l = 
    ψ₁ j (graft-leaf-from w ψ₀ j l)

  graft-assoc-decor-right : {i : I} (w : W P i)
    → (ψ₀ : Decor (Fr P) w (W P)) (ψ₁ : GADecor w ψ₀)
    → Decor (Fr P) w (W P)
  graft-assoc-decor-right w ψ₀ ψ₁ j l =
    graft (ψ₀ j l) (λ k l' → ψ₁ k (j , l , l'))
    
  -- grafting is associative
  graft-assoc : {i : I} (w : W P i)
    → (ψ₀ : Decor (Fr P) w (W P)) (ψ₁ : GADecor w ψ₀)
    → graft (graft w ψ₀) (graft-assoc-decor-left w ψ₀ ψ₁) ==
      graft w (graft-assoc-decor-right w ψ₀ ψ₁)
  graft-assoc (lf i) ψ₀ ψ₁ = idp
  graft-assoc (nd (f , ϕ)) ψ₀ ψ₁ =
    let ψ₀' j p k l = ψ₀ k (j , p , l)
        ψ₁' j p k t = ψ₁ k (fst t , (j , p , fst (snd t)) , snd (snd t))
        g-assoc j p = graft-assoc (ϕ j p) (ψ₀' j p) (ψ₁' j p)
    in ap (λ x → nd (f , x)) (Decor-== P g-assoc)

  -- graft-assoc leaf constructors
  graft-assoc-leaf-to-left : {i : I} (w : W P i)
    → (ψ₀ : Decor (Fr P) w (W P)) (ψ₁ : GADecor w ψ₀)
    → (j₀ : I) (l₀ : Leaf P w j₀) (j₁ : I) (l₁ : Leaf P (ψ₀ j₀ l₀) j₁)
    → (j₂ : I) (l₂ : Leaf P (ψ₁ j₁ (j₀ , l₀ , l₁)) j₂)
    → Leaf P (graft (graft w ψ₀) (graft-assoc-decor-left w ψ₀ ψ₁)) j₂
  graft-assoc-leaf-to-left w ψ₀ ψ₁ j₀ l₀ j₁ l₁ j₂ l₂ = 
    graft-lf-to {w = graft w ψ₀} (j₁ , graft-lf-to {w = w} (j₀ , l₀ , l₁) ,
      transport! (λ x → Leaf P (ψ₁ j₁ x) j₂) (graft-leaf-from-to w ψ₀ j₁ (j₀ , l₀ , l₁)) l₂)

  graft-assoc-leaf-to-right : {i : I} (w : W P i)
    → (ψ₀ : Decor (Fr P) w (W P)) (ψ₁ : GADecor w ψ₀)
    → (j₀ : I) (l₀ : Leaf P w j₀) (j₁ : I) (l₁ : Leaf P (ψ₀ j₀ l₀) j₁)
    → (j₂ : I) (l₂ : Leaf P (ψ₁ j₁ (j₀ , l₀ , l₁)) j₂)
    → Leaf P (graft w (graft-assoc-decor-right w ψ₀ ψ₁)) j₂
  graft-assoc-leaf-to-right w ψ₀ ψ₁ j₀ l₀ j₁ l₁ j₂ l₂ =
    graft-lf-to {w = w} (j₀ , l₀ , graft-lf-to {w = ψ₀ j₀ l₀} (j₁ , l₁ , l₂))
    
  -- The action of associativity on leaves
  graft-assoc-lf-ovr : {i : I} (w : W P i)
    → (ψ₀ : Decor (Fr P) w (W P)) (ψ₁ : GADecor w ψ₀)
    → (j₀ : I) (l₀ : Leaf P w j₀) (j₁ : I) (l₁ : Leaf P (ψ₀ j₀ l₀) j₁)
    → (j₂ : I) (l₂ : Leaf P (ψ₁ j₁ (j₀ , l₀ , l₁)) j₂)
    → graft-assoc-leaf-to-left w ψ₀ ψ₁ j₀ l₀ j₁ l₁ j₂ l₂ ==
      graft-assoc-leaf-to-right w ψ₀ ψ₁ j₀ l₀ j₁ l₁ j₂ l₂
        [ (λ x → Leaf P x j₂) ↓ graft-assoc w ψ₀ ψ₁ ]
  graft-assoc-lf-ovr (lf i) ψ₀ ψ₁ .i idp j₁ l₁ j₂ l₂ = idp
  graft-assoc-lf-ovr (nd (f , ϕ)) ψ₀ ψ₁ j₀ (k₀ , p₀ , l₀) j₁ l₁ j₂ l₂ =
    let ψ₀' j p k l = ψ₀ k (j , p , l)
        ψ₁' j p k t = ψ₁ k (fst t , (j , p , fst (snd t)) , snd (snd t))
        g-assoc j p = graft-assoc (ϕ j p) (ψ₀' j p) (ψ₁' j p)
        g x = fst x , (k₀ , p₀ , fst (snd x)) , snd (snd x)
        q = graft-leaf-from-to (ϕ k₀ p₀) (ψ₀' k₀ p₀) j₁ (j₀ , l₀ , l₁)
    in ↓-ap-in (λ x → Leaf P x j₂) (λ x → nd (f , x))
               (↓-nd-Leaf-ih P g-assoc k₀ p₀
                 (ap (λ x → graft-lf-to (j₁ , graft-lf-to (j₀ , l₀ , l₁) , x))
                     (! (transp!-ap (λ x → Leaf P (ψ₁ j₁ x) j₂) g q l₂)) ∙ᵈ
                 graft-assoc-lf-ovr (ϕ k₀ p₀) (ψ₀' k₀ p₀) (ψ₁' k₀ p₀) j₀ l₀ j₁ l₁ j₂ l₂))

  -- The action of associativity on nodes

  -- There are 3 possibilities depending on the position
  -- of the node in the iterated graft
  
  -- Left
  graft-assoc-nd-left : {i : I} (w : W P i)
    → (ψ₀ : ∀ j → Leaf P w j → W P j)
    → (ψ₁ : ∀ k → (t : Σ I (λ j → Σ (Leaf P w j) (λ l → Leaf P (ψ₀ j l) k))) → W P k)
    → (g : Ops P) (n : Node P w g)
    →  graft-nd-to {w = graft w ψ₀} (inl (graft-nd-to {w = w} (inl n)))
    == graft-nd-to {w = w} (inl n) [ (λ x → Node P x g) ↓ graft-assoc w ψ₀ ψ₁ ]
  graft-assoc-nd-left (lf i) ψ₀ ψ₁ g (lift ())
  graft-assoc-nd-left (nd (f , ϕ)) ψ₀ ψ₁ ._ (inl idp) =
    let ψ₀' j p k l = ψ₀ k (j , p , l)
        ψ₁' j p k t = ψ₁ k (fst t , (j , p , fst (snd t)) , snd (snd t))
        g-assoc j p = graft-assoc (ϕ j p) (ψ₀' j p) (ψ₁' j p)
    in ↓-ap-in (λ x → Node P x (_ , f)) (λ x → nd (f , x))
               (↓-Node-here-in P (Decor-== P g-assoc))
               
  graft-assoc-nd-left (nd (f , ϕ)) ψ₀ ψ₁ g (inr (j₀ , p₀ , n)) =
    let ψ₀' j p k l = ψ₀ k (j , p , l)
        ψ₁' j p k t = ψ₁ k (fst t , (j , p , fst (snd t)) , snd (snd t))
        g-assoc j p = graft-assoc (ϕ j p) (ψ₀' j p) (ψ₁' j p)
    in ↓-ap-in (λ x → Node P x g) (λ x → nd (f , x))
               (↓-Node-there-in P g-assoc j₀ p₀
                 (graft-assoc-nd-left (ϕ j₀ p₀) (ψ₀' j₀ p₀) (ψ₁' j₀ p₀) g n))

  -- Mid
  graft-assoc-nd-mid : {i : I} (w : W P i)
    → (ψ₀ : ∀ j → Leaf P w j → W P j)
    → (ψ₁ : ∀ k → (t : Σ I (λ j → Σ (Leaf P w j) (λ l → Leaf P (ψ₀ j l) k))) → W P k)
    → (g : Ops P) (j : I) (l : Leaf P w j) (n : Node P (ψ₀ j l) g)
    →  graft-nd-to {w = graft w ψ₀} (inl (graft-nd-to {w = w} (inr (j , l , n))))
    == graft-nd-to {w = w} (inr (j  , l , graft-nd-to {w = ψ₀ j l} (inl n)))
        [ (λ x → Node P x g) ↓ graft-assoc w ψ₀ ψ₁ ]
  graft-assoc-nd-mid (lf i) ψ₀ ψ₁ g .i idp n = idp
  graft-assoc-nd-mid (nd (f , ϕ)) ψ₀ ψ₁ g j (j₀ , p₀ , l) n = 
    let ψ₀' j p k l = ψ₀ k (j , p , l)
        ψ₁' j p k t = ψ₁ k (fst t , (j , p , fst (snd t)) , snd (snd t))
        g-assoc j p = graft-assoc (ϕ j p) (ψ₀' j p) (ψ₁' j p)
    in ↓-ap-in (λ x → Node P x g) (λ x → nd (f , x))
          (↓-Node-there-in P g-assoc j₀ p₀
            (graft-assoc-nd-mid (ϕ j₀ p₀) (ψ₀' j₀ p₀) (ψ₁' j₀ p₀) g j l n))

  -- Right
  graft-assoc-nd-right : {i : I} (w : W P i)
    → (ψ₀ : ∀ j → Leaf P w j → W P j)
    → (ψ₁ : ∀ k → (t : Σ I (λ j → Σ (Leaf P w j) (λ l → Leaf P (ψ₀ j l) k))) → W P k)
    → (g : Ops P) (j : I) (l₀ : Leaf P w j)
    → (k : I) (l₁ : Leaf P (ψ₀ j l₀) k) (n : Node P (ψ₁ k (j , l₀ , l₁)) g)
    → graft-nd-to {w = graft w ψ₀} (inr (k , graft-lf-to {w = w} (j , l₀ , l₁) ,
        transport! (λ x → Node P (ψ₁ k x) g) (graft-leaf-from-to w ψ₀ k (j , l₀ , l₁)) n))
    == graft-nd-to {w = w} (inr (j , l₀ , graft-nd-to {w = ψ₀ j l₀} (inr (k , l₁ , n))))
        [ (λ x → Node P x g) ↓ graft-assoc w ψ₀ ψ₁ ]
  graft-assoc-nd-right (lf i) ψ₀ ψ₁ g .i idp k l₁ n = idp
  graft-assoc-nd-right (nd (f , ϕ)) ψ₀ ψ₁ g j (j₀ , p₀ , l₀) k l₁ n = 
    let ψ₀' j p k l = ψ₀ k (j , p , l)
        ψ₁' j p k t = ψ₁ k (fst t , (j , p , fst (snd t)) , snd (snd t))
        g-assoc j p = graft-assoc (ϕ j p) (ψ₀' j p) (ψ₁' j p)
        σ x = fst x , (j₀ , p₀ , fst (snd x)) , snd (snd x)
        pth = graft-leaf-from-to (ϕ j₀ p₀) (λ k₁ l → ψ₀ k₁ (j₀ , p₀ , l)) k (j , l₀ , l₁)
    in ↓-ap-in (λ x → Node P x g) (λ x → nd (f , x))
         (↓-Node-there-in P g-assoc j₀ p₀
           ((ap (λ x → graft-nd-to {w = graft (ϕ j₀ p₀) (ψ₀' j₀ p₀)} (inr (k , graft-lf-to (j , l₀ , l₁) , x)))
                (! (transp!-ap (λ x → Node P (ψ₁ k x) g) σ pth n))) ∙ᵈ
             graft-assoc-nd-right (ϕ j₀ p₀) (ψ₀' j₀ p₀) (ψ₁' j₀ p₀) g j l₀ k l₁ n))

  -- Some useful path-over principles....
  -- (the naming conventions here really need to be looked at ...)
  ↓-graft-Leaf-ih₀ : {i j : I} {w : W P i}
    → {ψ₀ ψ₁ : Decor (Fr P) w (W P)} (e : ψ₀ == ψ₁)
    → (k : I) (l : Leaf P w k)
    → {l₀ : Leaf P (ψ₀ k l) j} {l₁ : Leaf P (ψ₁ k l) j}
    → l₀ == l₁ [ (λ x → Leaf P x j) ↓ app= (app= e k) l ]
    → graft-lf-to (k , l , l₀) == graft-lf-to (k , l , l₁) [ (λ x → Leaf P (graft w x) j) ↓ e ]
  ↓-graft-Leaf-ih₀ idp k p idp = idp

  ↓-graft-Leaf-ih : {i j : I} {w : W P i}
    → {ψ₀ ψ₁ : Decor (Fr P) w (W P)} 
    → (H : (k : I) (l : Leaf P w k) → ψ₀ k l == ψ₁ k l)
    → (k : I) (l : Leaf P w k)
    → {l₀ : Leaf P (ψ₀ k l) j} {l₁ : Leaf P (ψ₁ k l) j}
    → l₀ == l₁ [ (λ x → Leaf P x j) ↓ H k l ]
    → graft-lf-to (k , l , l₀) == graft-lf-to (k , l , l₁) [ (λ x → Leaf P (graft w x) j) ↓ Decor-== (Fr P) H ]
  ↓-graft-Leaf-ih H k l {l₀} {l₁} q =
    ↓-graft-Leaf-ih₀ (Decor-== (Fr P) H) k l
      (transport (λ y → l₀ == l₁ [ (λ x → Leaf P x _) ↓ y ])
                 (Decor-==-β (Fr P) H k l) q)

  ↓-graft-Node-left : {i : I} {w : W P i}
    → {ψ₀ ψ₁ : Decor (Fr P) w (W P)} (e : ψ₀ == ψ₁)
    → {g : Ops P} {n₀ : Node P w g} {n₁ : Node P w g} (p : n₀ == n₁)
    → graft-nd-to (inl n₀) == graft-nd-to (inl n₁) [ (λ x → Node P (graft w x) g) ↓ e ]
  ↓-graft-Node-left idp idp = idp

  ↓-graft-Node-right₀ : {i : I} {w : W P i}
    → {ψ₀ ψ₁ : Decor (Fr P) w (W P)} (e : ψ₀ == ψ₁)
    → {j : I} {l : Leaf P w j}
    → {g : Ops P} {n₀ : Node P (ψ₀ j l) g} {n₁ : Node P (ψ₁ j l) g}
    → n₀ == n₁ [ (λ x → Node P x g) ↓ app= (app= e j) l ]
    → graft-nd-to (inr (j , l , n₀)) == graft-nd-to (inr (j , l , n₁)) [ (λ x → Node P (graft w x) g) ↓ e ]
  ↓-graft-Node-right₀ idp idp = idp

  ↓-graft-Node-right : {i : I} {w : W P i}
    → {ψ₀ ψ₁ : Decor (Fr P) w (W P)} 
    → (H : (k : I) (l : Leaf P w k) → ψ₀ k l == ψ₁ k l)
    → {j : I} {l : Leaf P w j}
    → {g : Ops P} {n₀ : Node P (ψ₀ j l) g} {n₁ : Node P (ψ₁ j l) g}
    → n₀ == n₁ [ (λ x → Node P x g) ↓ H j l ]
    → graft-nd-to (inr (j , l , n₀)) == graft-nd-to (inr (j , l , n₁))
        [ (λ x → Node P (graft w x) g) ↓ Decor-== (Fr P) H ]
  ↓-graft-Node-right H {j} {l} {g} {n₀} {n₁} q = ↓-graft-Node-right₀ (Decor-== (Fr P) H)
    (transport (λ y → n₀ == n₁ [ (λ x → Node P x g) ↓ y ]) (Decor-==-β (Fr P) H j l) q)
