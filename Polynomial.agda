{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util

-- 
-- We will try to use the following conventions for naming:
--
--  P, Q, R ... : Poly
--  i, j, k ... : I     (sorts ...)
--  f, g, h ... : Op    (operations ...)
--  p, q, r ... : Param (parameters ...)
--

module Polynomial where

  record Poly {ℓ} (I : Type ℓ) : Type (lsucc ℓ) where
    field
      Op : I → Type ℓ
      Param : {i : I} → Op i → I → Type ℓ

  open Poly public

  Ops : ∀ {ℓ} {I : Type ℓ} (P : Poly I) → Type ℓ
  Ops {I = I} P = Σ I (Op P)

  Arity : ∀ {ℓ} {I : Type ℓ} (P : Poly I)
    → {i : I} (f : Op P i) → Type ℓ
  Arity {I = I} P f = Σ I (Param P f)
  
  Decor : ∀ {ℓ} {I : Type ℓ} (P : Poly I)
    → {i : I} (f : Op P i) (X : I → Type ℓ)
    → Type ℓ
  Decor P f X = ∀ j → Param P f j → X j

  ⟦_⟧ : ∀ {ℓ} {I : Type ℓ} (P : Poly I) → (I → Type ℓ) → I → Type ℓ
  ⟦ P ⟧ X i = Σ (Op P i) (λ f → ∀ j → Param P f j → X j)

  ⟦_⟧f : ∀ {ℓ} {I : Type ℓ} (P : Poly I) {X Y : I → Type ℓ}
    → (ψ : (i : I) → X i → Y i)
    → (i : I) → ⟦ P ⟧ X i → ⟦ P ⟧ Y i
  ⟦ P ⟧f ψ i (f , ϕ)= f , λ j p → ψ j (ϕ j p)

  module _ {ℓ} {I : Type ℓ} (P : Poly I) where

    data W : I → Type ℓ where
      lf : (i : I) → W i
      nd : {i : I} → ⟦ P ⟧ W i → W i

    Leaf : {i : I} (w : W i) → I → Type ℓ
    Leaf (lf i) j = i == j
    Leaf (nd (f , ϕ)) j = Σ I (λ k → Σ (Param P f k) (λ p → Leaf (ϕ k p) j))

    Node : {i : I} (w : W i) → Ops P → Type ℓ
    Node (lf i) p = Lift ⊥
    Node (nd {i} (f , ϕ)) jg = ((i , f) == jg) ⊔ Σ I (λ k → Σ (Param P f k) (λ p → Node (ϕ k p) jg))

    Frame : {i : I} (w : W i) (f : Op P i) → Type ℓ
    Frame w f = (j : I) → Leaf w j ≃ Param P f j

    InFrame : Ops P → Type ℓ
    InFrame (i , f) = Σ (W i) (λ w → Frame w f)

    OutFrame : {i : I} → W i → Type ℓ
    OutFrame {i} w = Σ (Op P i) (Frame w)

    PolyRel : Type (lsucc ℓ)
    PolyRel = (f : Ops P) → InFrame f → Type ℓ

    corolla : {i : I} (f : Op P i) → W i
    corolla {i} f = nd (f , λ j p → lf j)

    -- Defining the adjoint for this equivalence directly
    -- gives better definitional behavior for the substitution
    -- laws, which is why we take the trouble.
    corolla-frm : {i : I} (f : Op P i)
      → (j : I) → Leaf (corolla f) j ≃ Param P f j
    corolla-frm f j = to ,
      record { g = from ;
               f-g = (λ x → idp) ;
               g-f = from-to ;
               adj = adj }

      where to : Leaf (corolla f) j → Param P f j
            to (_ , p , l) = transport (Param P f) l p

            from : Param P f j → Leaf (corolla f) j
            from p = (j , p , idp) 

            from-to : (l : Leaf (corolla f) j) → from (to l) == l
            from-to (_ , p , idp) = idp

            adj : (l : Leaf (corolla f) j) → ap to (from-to l) == idp
            adj (j , p , idp) = idp

  --
  --  Path-overs for Frames in each variable
  --

  module _ {ℓ} {I : Type ℓ} (P : Poly I) where
    
    ↓-Op-Frame-in : {i : I} {w : W P i}
      → {f g : Op P i} (e : f == g)
      → {α : Frame P w f} {β : Frame P w g}
      → (t : (j : I) (l : Leaf P w j) → –> (α j) l == –> (β j) l [ (λ x → Param P x j) ↓ e ])
      → α == β [ Frame P w ↓ e ]
    ↓-Op-Frame-in idp t = λ= (λ j → equiv-== (t j))

    ↓-Op-Frame-out : {i : I} {w : W P i}
      → {f g : Op P i} (e : f == g)
      → {α : Frame P w f} {β : Frame P w g}
      → α == β [ Frame P w ↓ e ]
      → (j : I) (l : Leaf P w j)
      → –> (α j) l == –> (β j) l [ (λ x → Param P x j) ↓ e ]
    ↓-Op-Frame-out idp idp j l = idp

    ↓-W-Frame-in : {i : I} {f : Op P i}
      → {w₀ w₁ : W P i} {e : w₀ == w₁}
      → {α : Frame P w₀ f} {β : Frame P w₁ f}
      → (t : (j : I) (l₀ : Leaf P w₀ j) (l₁ : Leaf P w₁ j)
             → (r : l₀ == l₁ [ (λ x → Leaf P x j) ↓ e ])
             → –> (α j) l₀ == –> (β j) l₁)
      → α == β [ (λ x → Frame P x f) ↓ e ]
    ↓-W-Frame-in {e = idp} t = λ= (λ j → equiv-== (λ l → t j l l idp))

    ↓-W-Frame-out : {i : I} {f : Op P i}
      → {w₀ w₁ : W P i} {e : w₀ == w₁}
      → {α : Frame P w₀ f} {β : Frame P w₁ f}
      → α == β [ (λ x → Frame P x f) ↓ e ]
      → (j : I) (l₀ : Leaf P w₀ j) (l₁ : Leaf P w₁ j)
      → (r : l₀ == l₁ [ (λ x → Leaf P x j) ↓ e ])
      → –> (α j) l₀ == –> (β j) l₁
    ↓-W-Frame-out {e = idp} idp j l .l idp = idp

    Decor-== : {X : I → Type ℓ} {i : I} {f : Op P i}
      → {ϕ₀ ϕ₁ : Decor P f X}
      → (H : (j : I) (p : Param P f j) → ϕ₀ j p == ϕ₁ j p)
      → ϕ₀ == ϕ₁
    Decor-== H = λ= (λ j → λ= (λ p → H j p))

    Decor-==-β : {X : I → Type ℓ} {i : I} {f : Op P i}
      → {ϕ₀ ϕ₁ : Decor P f X}
      → (H : (j : I) (p : Param P f j) → ϕ₀ j p == ϕ₁ j p)
      → (j : I) (p : Param P f j)
      → H j p == app= (app= (Decor-== H) j) p
    Decor-==-β H j p = H j p =⟨ ! (app=-β (H j) p) ⟩
                       app= (λ= (H j)) p =⟨ ap (λ x → app= x p) (! (app=-β (λ k → λ= (H k)) j)) ⟩ 
                       app= (app= (Decor-== H) j) p ∎ 


    -- Path-overs for inductions relating leaves and nodes
    -- for the node constructor with equal decorations
    
    ↓-nd-Leaf-ih₀ : {i j : I} {f : Op P i}
      → {ϕ₀ ϕ₁ : Decor P f (W P)} (e : ϕ₀ == ϕ₁)
      → (k : I) (p : Param P f k)
      → {l₀ : Leaf P (ϕ₀ k p) j} {l₁ : Leaf P (ϕ₁ k p) j}
      → l₀ == l₁ [ (λ x → Leaf P x j) ↓ app= (app= e k) p ]
      → (k , p , l₀) == (k , p , l₁) [ (λ x → Leaf P (nd (f , x)) j) ↓ e ]
    ↓-nd-Leaf-ih₀ idp k p idp = idp

    ↓-nd-Leaf-ih : {i j : I} {f : Op P i}
      → {ϕ₀ ϕ₁ : Decor P f (W P)}
      → (H : (j : I) (p : Param P f j) → ϕ₀ j p == ϕ₁ j p)
      → (k : I) (p : Param P f k)
      → {l₀ : Leaf P (ϕ₀ k p) j} {l₁ : Leaf P (ϕ₁ k p) j}
      → l₀ == l₁ [ (λ x → Leaf P x j) ↓ H k p ]
      → (k , p , l₀) == (k , p , l₁) [ (λ x → Leaf P (nd (f , x)) j) ↓ Decor-== H ]
    ↓-nd-Leaf-ih H k p {l₀} {l₁} q = ↓-nd-Leaf-ih₀ (Decor-== H) k p
      (transport (λ y → l₀ == l₁ [ (λ x → Leaf P x _) ↓ y ]) (Decor-==-β H k p) q )

    ↓-Node-here-in : {i : I} {f : Op P i}
      → {ϕ₀ ϕ₁ : Decor P f (W P)} (e : ϕ₀ == ϕ₁)
      → inl idp == inl idp [ (λ x → Node P (nd (f , x)) (i , f)) ↓ e ]
    ↓-Node-here-in idp = idp

    ↓-Node-there-in₀ : {i : I} {f : Op P i}
      → {ϕ₀ ϕ₁ : Decor P f (W P)} (e : ϕ₀ == ϕ₁)
      → {g : Ops P} (j : I) (p : Param P f j)
      → {n₀ : Node P (ϕ₀ j p) g} {n₁ : Node P (ϕ₁ j p) g}
      → (q : n₀ == n₁ [ (λ x → Node P x g) ↓ app= (app= e j) p ])
      → inr (j , p , n₀) == inr (j , p , n₁) [ (λ x → Node P (nd (f , x)) g) ↓ e ]
    ↓-Node-there-in₀ idp j p idp = idp

    ↓-Node-there-in : {i : I} {f : Op P i}
      → {ϕ₀ ϕ₁ : Decor P f (W P)} 
      → (H : (j : I) (p : Param P f j) → ϕ₀ j p == ϕ₁ j p)
      → {g : Ops P} (j : I) (p : Param P f j)
      → {n₀ : Node P (ϕ₀ j p) g} {n₁ : Node P (ϕ₁ j p) g}
      → (q : n₀ == n₁ [ (λ x → Node P x g) ↓ H j p ])
      → inr (j , p , n₀) == inr (j , p , n₁) [ (λ x → Node P (nd (f , x)) g) ↓ Decor-== H ]
    ↓-Node-there-in H {g} j p {n₀} {n₁} q = ↓-Node-there-in₀ (Decor-== H) j p
      (transport (λ y → n₀ == n₁ [ (λ x → Node P x g) ↓ y ]) (Decor-==-β H j p) q)

