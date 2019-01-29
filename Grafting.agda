{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial

module Grafting {ℓ} {I : Type ℓ} (P : Poly I) where

  graft : {i : I} (w : W P i) (ψ : ∀ j → Leaf P w j → W P j) → W P i
  graft (lf i) ψ = ψ i idp
  graft (nd (f ,  ϕ)) ψ = 
    let ψ' j p k l = ψ k (j , p , l)
        ϕ' j p = graft (ϕ j p) (ψ' j p)
    in nd (f ,  ϕ')

  --
  --  Leaves in a graft
  --

  graft-leaf-to : {i : I} (w : W P i) (ψ : ∀ j → Leaf P w j → W P j) (k : I)
    → Σ I (λ j → Σ (Leaf P w j) (λ l → Leaf P (ψ j l) k))
    → Leaf P (graft w ψ) k
  graft-leaf-to (lf i) ψ k (.i , idp , l) = l
  graft-leaf-to (nd (f ,  ϕ)) ψ k (j₁ , (j₀ , p , l₀) , l₁) = 
    let ψ' j p k l = ψ k (j , p , l)
    in (j₀ , p , graft-leaf-to (ϕ j₀ p) (ψ' j₀ p) k (j₁ , l₀ , l₁))

  graft-leaf-from : {i : I} (w : W P i) (ψ : ∀ j → Leaf P w j → W P j) (k : I)
    → Leaf P (graft w ψ) k
    → Σ I (λ j → Σ (Leaf P w j) (λ l → Leaf P (ψ j l) k))
  graft-leaf-from (lf i) ψ k l = i , idp , l
  graft-leaf-from (nd (f ,  ϕ)) ψ k (j , p , l) = 
    let (s , t , u) = graft-leaf-from (ϕ j p) (λ k l → ψ k (j , p , l)) k l
    in s , (j , p , t) , u

  abstract


    graft-leaf-to-from : {i : I} (w : W P i) (ψ : ∀ j → Leaf P w j → W P j)
      → (k : I) (l : Leaf P (graft w ψ) k)
      → graft-leaf-to w ψ k (graft-leaf-from w ψ k l) == l
    graft-leaf-to-from (lf i) ψ k l = idp
    graft-leaf-to-from (nd (f ,  ϕ)) ψ k (j , p , l) =
      let ψ' j p k l = ψ k (j , p , l)
      in ap (λ x → (j , p , x)) (graft-leaf-to-from (ϕ j p) (ψ' j p) k l) 

    graft-leaf-from-to : {i : I} (w : W P i) (ψ : ∀ j → Leaf P w j → W P j) (k : I)
      → (l : Σ I (λ j → Σ (Leaf P w j) (λ l → Leaf P (ψ j l) k)))
      → graft-leaf-from w ψ k (graft-leaf-to w ψ k l) == l
    graft-leaf-from-to (lf i) ψ k (.i , idp , l₁) = idp
    graft-leaf-from-to (nd (f ,  ϕ)) ψ k (j₁ , (j₀ , p , l₀) , l₁) =
      let ψ' j p k l = ψ k (j , p , l)
          ih = graft-leaf-from-to (ϕ j₀ p) (ψ' j₀ p) k (j₁ , l₀ , l₁)
      in ap (λ x → (fst x , (j₀ , p , fst (snd x)) , snd (snd x))) ih

  graft-leaf-eqv : {i : I} (w : W P i) (ψ : ∀ j → Leaf P w j → W P j) (k : I)
    → Σ I (λ j → Σ (Leaf P w j) (λ l → Leaf P (ψ j l) k)) ≃ Leaf P (graft w ψ) k
  graft-leaf-eqv w ψ k =
    equiv (graft-leaf-to w ψ k) (graft-leaf-from w ψ k)
          (graft-leaf-to-from w ψ k) (graft-leaf-from-to w ψ k)

  --
  --  Nodes in a graft
  --

  graft-node-to : {i : I} (w : W P i)
    → (ψ : ∀ j → Leaf P w j → W P j) (g : Ops P)
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
    → (ψ : ∀ j → Leaf P w j → W P j) (g : Ops P)
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
    -- This can also be written as a map ...
    ⊔-rec (λ n → inl (inr (j , p , n)))
          (λ t → let (k , l , n) = t in inr ((k , (j , p , l) , n)))

  abstract

    graft-node-to-from : {i : I} (w : W P i)
      → (ψ : ∀ j → Leaf P w j → W P j) (g : Ops P)
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
      → (ψ : ∀ j → Leaf P w j → W P j) (g : Ops P)
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
    → (ψ : ∀ j → Leaf P w j → W P j)
    → (g : Ops P)
    → Node P w g ⊔ Σ I (λ k → Σ (Leaf P w k) (λ l → Node P (ψ k l) g))
      ≃ Node P (graft w ψ) g
  graft-node-eqv w ψ g =
    equiv (graft-node-to w ψ g) (graft-node-from w ψ g)
          (graft-node-to-from w ψ g) (graft-node-from-to w ψ g)

  --
  -- Basic laws of grafting
  --

  -- grafting is unital
  graft-unit : {i : I} (w : W P i) → w == graft w (λ j l → lf j) 
  graft-unit (lf i) = idp
  graft-unit (nd (f , ϕ)) =
    ap (λ x → nd (f , x))
       (Decor-== P (λ j p → graft-unit (ϕ j p)))

  -- graft-unit-lf-to : {i : I} (w : W P i) (j : I)
  --   → Leaf P (graft w (λ k _ → lf k)) j
  --   → Leaf P w j
  -- graft-unit-lf-to w j l =
  --   let (k , l₀ , l₁) = graft-leaf-from w (λ k _ → lf k) j l
  --   in transport (Leaf P w) l₁ l₀

  -- graft-unit-lf-from : {i : I} (w : W P i) (j : I)
  --   → Leaf P w j
  --   → Leaf P (graft w (λ k _ → lf k)) j
  -- graft-unit-lf-from w j l =
  --   graft-leaf-to w (λ k _ → lf k) j (j , l , idp)

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

  -- grafting is associative
  graft-assoc : {i : I} (w : W P i)
    → (ψ₀ : ∀ j → Leaf P w j → W P j)
    → (ψ₁ : ∀ k → (t : Σ I (λ j → Σ (Leaf P w j) (λ l → Leaf P (ψ₀ j l) k))) → W P k)
    → graft (graft w ψ₀) (λ j l → ψ₁ j (graft-leaf-from w ψ₀ j l)) ==
      graft w (λ j l₀ → graft (ψ₀ j l₀) (λ k l₁ → ψ₁ k (j , l₀ , l₁)))
  graft-assoc (lf i) ψ₀ ψ₁ = idp
  graft-assoc (nd (f , ϕ)) ψ₀ ψ₁ = ap (λ x → nd (f , x))
    (λ= (λ j → λ= (λ p → graft-assoc (ϕ j p) (λ k l → ψ₀ k (j , p , l))
      (λ k t → ψ₁ k (fst t , (j , p , fst (snd t)) , snd (snd t))))))


