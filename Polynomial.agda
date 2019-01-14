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

    corolla-frm : {i : I} (f : Op P i)
      → (j : I) → Leaf (corolla f) j ≃ Param P f j
    corolla-frm f j = equiv to from (λ _ → idp) from-to

      where to : Leaf (corolla f) j → Param P f j
            to (_ , p , idp) = p

            from : Param P f j → Leaf (corolla f) j
            from p = (j , p , idp) 

            from-to : (l : Leaf (corolla f) j) → from (to l) == l
            from-to (_ , p , idp) = idp


  --
  --  Polynomial Magmas and Slicing
  --

  record PolyMagma {ℓ} {I : Type ℓ} (P : Poly I) : Type ℓ where
    constructor mgm
    field
      μ : {i : I} (w : W P i) → Op P i
      μ-frm : {i : I} (w : W P i) → Frame P w (μ w)

  open PolyMagma public

  -- The slice of a polynomial by a relation
  _//_ : ∀ {ℓ} {I : Type ℓ} (P : Poly I) (R : PolyRel P) → Poly (Ops P)
  Op (P // R) f = Σ (InFrame P f) (R f)
  Param (P // R) ((w , _) , _) = Node P w

  -- The relation induced by a magma
  ⟪_⟫ : ∀ {ℓ} {I : Type ℓ} {P : Poly I} (M : PolyMagma P) → PolyRel P
  ⟪_⟫ {P = P} M (i , f) (w , α) = Path {A = OutFrame P w}
    (μ M w , μ-frm M w) (f , α)

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
      → {w₀ w₁ : W P i} (e : w₀ == w₁)
      → (α : Frame P w₀ f) (β : Frame P w₁ f)
      → (t : (j : I) (l₀ : Leaf P w₀ j) (l₁ : Leaf P w₁ j)
             → (r : l₀ == l₁ [ (λ x → Leaf P x j) ↓ e ])
             → –> (α j) l₀ == –> (β j) l₁)
      → α == β [ (λ x → Frame P x f) ↓ e ]
    ↓-W-Frame-in idp α β t = λ= (λ j → equiv-== (λ l → t j l l idp))

    ↓-W-Frame-out : {i : I} {f : Op P i}
      → {w₀ w₁ : W P i} (e : w₀ == w₁)
      → (α : Frame P w₀ f) (β : Frame P w₁ f)
      → α == β [ (λ x → Frame P x f) ↓ e ]
      → (j : I) (l₀ : Leaf P w₀ j) (l₁ : Leaf P w₁ j)
      → (r : l₀ == l₁ [ (λ x → Leaf P x j) ↓ e ])
      → –> (α j) l₀ == –> (β j) l₁
    ↓-W-Frame-out idp α .α idp j l .l idp = idp

    Decor-== : {X : I → Type ℓ} {i : I} {f : Op P i}
      → {δ₀ δ₁ : Decor P f X}
      → (ϕ : (j : I) (p : Param P f j) → δ₀ j p == δ₁ j p)
      → δ₀ == δ₁
    Decor-== ϕ = λ= (λ j → λ= (λ p → ϕ j p))


