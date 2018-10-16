{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial

module WPaths {ℓ} {I : Type ℓ} (P : Poly I) where

  WCodes : {i : I} → W P i → W P i → Type ℓ
  WCodes (lf i) (lf .i) = Lift ⊤
  WCodes (lf i) (nd _) = Lift ⊥
  WCodes (nd _) (lf i) = Lift ⊥
  WCodes (nd (f , ϕ)) (nd (g , ψ)) = (f , ϕ) == (g , ψ)

  encode : {i : I} (w₀ w₁ : W P i) (p : w₀ == w₁) → WCodes w₀ w₁
  encode (lf i) .(lf i) idp = lift tt
  encode (nd (f , ϕ)) .(nd (f , ϕ)) idp = idp 

  decode : {i : I} (w₀ w₁ : W P i) (c : WCodes w₀ w₁) → w₀ == w₁
  decode (lf i) (lf .i) (lift tt) = idp
  decode (lf i) (nd (f , ϕ)) (lift ())
  decode (nd (f , ϕ)) (lf i) (lift ())
  decode (nd (f , ϕ)) (nd (g , ψ)) e = ap nd e

  decode-encode : {i : I} (w₀ w₁ : W P i) (p : w₀ == w₁)
    → decode w₀ w₁ (encode w₀ w₁ p) == p
  decode-encode (lf i) .(lf i) idp = idp
  decode-encode (nd (f , ϕ)) .(nd (f , ϕ)) idp = idp

  encode-decode : {i : I} (w₀ w₁ : W P i) (c : WCodes w₀ w₁)
    → encode w₀ w₁ (decode w₀ w₁ c) == c
  encode-decode (lf i) (lf .i) (lift tt) = idp
  encode-decode (lf i) (nd (f , ϕ)) (lift ())
  encode-decode (nd (f , ϕ)) (lf i) (lift ())
  encode-decode (nd (f , ϕ)) (nd .(f , ϕ)) idp = idp

  W=-eqv : {i : I} (w₀ w₁ : W P i) → (w₀ == w₁) ≃ WCodes w₀ w₁ 
  W=-eqv w₀ w₁ = equiv (encode w₀ w₁) (decode w₀ w₁)
    (encode-decode w₀ w₁) (decode-encode w₀ w₁)

  -- The above generic description can now be massaged
  -- into more natural looking constructors.  The above,
  -- however, is more fundamental and sometimes more
  -- useful.
  
  -- Decor : ∀ {ℓ} {I : Type ℓ} (P : Poly I)
  --   → {i : I} (f : Op P i) (X : I → Type ℓ)
  --   → Type ℓ
  -- Decor P f X = ∀ j → Param P f j → X j

  -- Decor= : (X : I → Type ℓ)
  --   → {i : I} {f g : Op P i} (e : f == g)
  --   → (ϕ : Decor P f X) (ψ : Decor P g X)
  --   → Type ℓ
  -- Decor= X {f = f} {g = g} e ϕ ψ =
  --   (j : I) (p : Param P f j) (q : Param P g j)
  --   → (r : p == q [ (λ x → Param P x j) ↓ e ])
  --   → ϕ j p == ψ j q 
  
  -- ↓-Decor-in : (X : I → Type ℓ)
  --   → {i : I} {f g : Op P i} (e : f == g)
  --   → (ϕ : Decor P f X) (ψ : Decor P g X)
  --   → Decor= X e ϕ ψ
  --   → ϕ == ψ [ (λ x → Decor P x X) ↓ e ]
  -- ↓-Decor-in X idp ϕ ψ d = λ= (λ j → λ= (λ p → d j p p idp))
  
  -- ↓-Decor-out : (X : I → Type ℓ)
  --   → {i : I} {f g : Op P i} (e : f == g)
  --   → (ϕ : Decor P f X) (ψ : Decor P g X)
  --   → ϕ == ψ [ (λ x → Decor P x X) ↓ e ]
  --   → Decor= X e ϕ ψ
  -- ↓-Decor-out X idp ϕ ψ idp j p .p idp = idp
