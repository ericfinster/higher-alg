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

  -- A consequence is the following:
  lf-eq-contr : (i : I) → is-contr (lf {P = P} i == lf i)
  lf-eq-contr i = equiv-preserves-level ((W=-eqv (lf i) (lf i))⁻¹)

  -- The above generic description can now be massaged
  -- into more natural looking constructors.  The above,
  -- however, is more fundamental and sometimes more
  -- useful.
  
  -- Decor : ∀ {ℓ} {I : Type ℓ} (P : Poly I)
  --   → {i : I} (f : Op P i) (X : I → Type ℓ)
  --   → Type ℓ
  -- Decor P f X = ∀ j → Param P f j → X j

  Decor= : (X : I → Type ℓ)
    → {i : I} {f g : Op P i} (e : f == g)
    → (ϕ : Decor P f X) (ψ : Decor P g X)
    → Type ℓ
  Decor= X {f = f} {g = g} e ϕ ψ =
    (j : I) (p : Param P f j) (q : Param P g j)
    → (r : p == q [ (λ x → Param P x j) ↓ e ])
    → ϕ j p == ψ j q 
  
  ↓-Decor-in : (X : I → Type ℓ)
    → {i : I} {f g : Op P i} (e : f == g)
    → (ϕ : Decor P f X) (ψ : Decor P g X)
    → Decor= X e ϕ ψ
    → ϕ == ψ [ (λ x → Decor P x X) ↓ e ]
  ↓-Decor-in X idp ϕ ψ d = λ= (λ j → λ= (λ p → d j p p idp))
  
  ↓-Decor-out : (X : I → Type ℓ)
    → {i : I} {f g : Op P i} (e : f == g)
    → (ϕ : Decor P f X) (ψ : Decor P g X)
    → ϕ == ψ [ (λ x → Decor P x X) ↓ e ]
    → Decor= X e ϕ ψ
  ↓-Decor-out X idp ϕ ψ idp j p .p idp = idp

  -- A next step is to characterize automorphisms of a graft.
  
  -- GraftData : I → Type ℓ
  -- GraftData i = Σ (W P i) (λ w → ∀ j → Leaf P w j → W P j)

  -- GraftCodes : {i : I} (γ₀ γ₁ : GraftData i) → Type ℓ
  -- GraftCodes (lf i , ψ₀) (lf .i , ψ₁) = ψ₀ i idp == ψ₁ i idp
  -- GraftCodes (lf i , ψ₀) (nd (f , ϕ) , ψ₁) = ψ₀ i idp == nd (f , λ j p → graft P (ϕ j p) (λ k l → ψ₁ k (j , p , l)))
  -- GraftCodes (nd (f , ϕ) , ψ₀) (lf i , ψ₁) = nd (f , λ j p → graft P (ϕ j p) (λ k l → ψ₀ k (j , p , l))) == ψ₁ i idp
  -- GraftCodes (nd (f , ϕ) , ψ₀) (nd (f' , ϕ') , ψ₁) = {!!}

  -- graft=-to : {i : I} (w : W P i) (ψ : ∀ j → Leaf P w j → W P j)
  --   → Path {A = GraftData i} (w , ψ) (w , ψ) 
  --   → graft P w ψ == graft P w ψ
  -- graft=-to w ψ e = ap (uncurry (graft P)) e

  -- graft=-from : {i : I} (w : W P i) (ψ : ∀ j → Leaf P w j → W P j)
  --   → graft P w ψ == graft P w ψ
  --   → Path {A = GraftData i} (w , ψ) (w , ψ) 
  -- graft=-from (lf i) ψ e = pair= idp {!uncurry!} -- and this is clearly true ...
  -- graft=-from (nd (f , ϕ)) ψ e = 
  --   let ϕ' j p = graft P (ϕ j p) (λ k l → ψ k (j , p , l))
  --       ih j p = graft=-from (ϕ j p) (λ k l → ψ k (j , p , l)) {!–> (W=-eqv (nd (f , ϕ')) (nd (f , ϕ'))) e!}
  --       blorp = –> (W=-eqv (nd (f , ϕ')) (nd (f , ϕ'))) e
  --   in pair= (ap nd (pair= (fst= blorp) {!snd= blorp!})) {!!}

  -- Right, you've understood that the above is false:
  -- Not every automorphism of a graft "splits".  An
  -- interesting idea is to try to characterize exactly
  -- those which do....

  -- And therefore the space of decoration equivalences is contractible!
  corolla-dec-contr : {i : I} (f : Op P i)
    → is-contr (Decor= (W P) {f = f} idp (λ j p → lf j) (λ j p → lf j))
  corolla-dec-contr f = Π-level (λ j → Π-level (λ p → Π-level (λ q → Π-level (λ x → lf-eq-contr j))))
