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

  W=-equiv : {i : I} {w₀ w₁ : W P i} → (w₀ == w₁) ≃ WCodes w₀ w₁ 
  W=-equiv {w₀ = w₀} {w₁ = w₁} = equiv (encode w₀ w₁) (decode w₀ w₁)
    (encode-decode w₀ w₁) (decode-encode w₀ w₁)

  -- A consequence is the following:
  lf-eq-contr : (i : I) → is-contr (lf {P = P} i == lf i)
  lf-eq-contr i = equiv-preserves-level ((W=-equiv)⁻¹)

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
    → {ϕ : Decor P f X} {ψ : Decor P g X}
    → Decor= X e ϕ ψ
    → ϕ == ψ [ (λ x → Decor P x X) ↓ e ]
  ↓-Decor-in X idp d = λ= (λ j → λ= (λ p → d j p p idp))
  
  ↓-Decor-out : (X : I → Type ℓ)
    → {i : I} {f g : Op P i} (e : f == g)
    → {ϕ : Decor P f X} {ψ : Decor P g X}
    → ϕ == ψ [ (λ x → Decor P x X) ↓ e ]
    → Decor= X e ϕ ψ
  ↓-Decor-out X idp idp j p .p idp = idp

  postulate

    Decor=-equiv : (X : I → Type ℓ)
      → {i : I} {f g : Op P i} (e : f == g)
      → (ϕ : Decor P f X) (ψ : Decor P g X)
      → (ϕ == ψ [ (λ x → Decor P x X) ↓ e ]) ≃ Decor= X e ϕ ψ

  corolla-dec-contr : {i : I} (f : Op P i)
    → is-contr (Decor= (W P) {f = f} idp (λ j p → lf j) (λ j p → lf j))
  corolla-dec-contr f = Π-level (λ j → Π-level (λ p → Π-level (λ q → Π-level (λ x → lf-eq-contr j))))

  --
  --  Level calculations
  --

  W-level-aux : ∀ {n} (op-lvl : (i : I) → has-level (S (S n)) (Op P i))
    → (i : I) → has-level-aux (S (S n)) (W P i)
  W-level-aux op-lvl i (lf .i) (lf .i) =
    contr-has-level (lf-eq-contr i)
  W-level-aux op-lvl i (lf .i) (nd (g , ψ)) =
    has-level-in (λ p → Empty-rec (lower (–> W=-equiv p)))
  W-level-aux op-lvl i (nd (f , ϕ)) (lf .i) =
    has-level-in (λ p → Empty-rec (lower (–> W=-equiv p)))
  W-level-aux op-lvl i (nd (f , ϕ)) (nd (g , ψ)) = equiv-preserves-level ((W=-equiv)⁻¹)
    ⦃ equiv-preserves-level (=Σ-econv (f , ϕ) (g , ψ))
      ⦃ Σ-level (has-level-apply (op-lvl i) f g)
          (λ e → equiv-preserves-level ((Decor=-equiv (W P) e ϕ ψ)⁻¹)
                 ⦃ Π-level (λ j → Π-level (λ p → Π-level (λ q → Π-level (λ r →
                   W-level-aux op-lvl j (ϕ j p) (ψ j q))))) ⦄ )⦄ ⦄

  W-level : ∀ {n} (op-lvl : (i : I) → has-level (S (S n)) (Op P i))
    → (i : I) → has-level (S (S n)) (W P i)
  W-level op-lvl i = has-level-in (W-level-aux op-lvl i)

  Leaf-level : ∀ {n} (arity-lvl : {i : I} (f : Op P i) → has-level n (Arity P f))
    → {i : I} (w : W P i) → has-level n (Σ I (Leaf P w))
  Leaf-level arity-lvl (lf i) = contr-has-level (pathfrom-is-contr i)
  Leaf-level arity-lvl (nd (f , ϕ)) = equiv-preserves-level switch-eqv
    ⦃ Σ-level (arity-lvl f) (λ p → Leaf-level arity-lvl (ϕ (fst p) (snd p))) ⦄

    where switch-eqv : Σ (Arity P f) (λ { (k , p) → Σ I (Leaf P (ϕ k p)) })
                       ≃ (Σ I (λ j → Σ I (λ k → Σ (Param P f k) (λ p → Leaf P (ϕ k p) j))))
          switch-eqv = equiv (λ { ((k , p) , (j , l)) → j , k , p , l })
                             (λ { (j , k , p , l) → ((k , p) , (j , l)) })
                             (λ { (j , k , p , l) → idp } )
                             (λ { ((k , p) , (j , l)) → idp })

  Node-level : ∀ {n} (arity-lvl : {i : I} (f : Op P i) → has-level (S (S n)) (Arity P f))
    → {i : I} (w : W P i) → has-level (S (S n)) (Σ (Ops P) (Node P w))
  Node-level arity-lvl (lf i) = equiv-preserves-level no-node ⦃ ⊥-level ⦄

    where no-node : ⊥ ≃ Σ (Ops P) (cst (Lift ⊥))
          no-node = equiv ⊥-elim (λ { (_ , ()) }) (λ { (_ , ()) }) ⊥-elim

  Node-level arity-lvl (nd (f , ϕ)) = equiv-preserves-level switch-eqv
    ⦃ Coprod-level (raise-level _ Unit-level) (Σ-level (arity-lvl f)
                   (λ p → Node-level arity-lvl (ϕ (fst p) (snd p)))) ⦄

    where switch-eqv : ⊤ ⊔ Σ (Arity P f) (λ { (k , p) → Σ (Ops P) (Node P (ϕ k p)) })
                       ≃ Σ (Ops P) (λ g → ((_ , f) == g) ⊔ Σ I (λ k → Σ (Param P f k) (λ p → Node P (ϕ k p) g)))
          switch-eqv = equiv to from to-from from-to

            where A = ⊤ ⊔ Σ (Arity P f) (λ { (k , p) → Σ (Ops P) (Node P (ϕ k p)) })
                  B = Σ (Ops P) (λ g → ((_ , f) == g) ⊔ Σ I (λ k → Σ (Param P f k) (λ p → Node P (ϕ k p) g)))

                  to : A → B
                  to (inl tt) = (_ , f) , (inl idp)
                  to (inr ((k , p) , ((j , g) , n))) = (j , g) , (inr (k , p , n))

                  from : B → A
                  from (._ , inl idp) = inl tt
                  from ((j , g) , inr (k , p , n)) = inr ((k , p) , ((j , g) , n))

                  to-from : (b : B) → to (from b) == b
                  to-from (._ , inl idp) = idp
                  to-from ((j , g) , inr (k , p , n)) = idp

                  from-to : (a : A) → from (to a) == a
                  from-to (inl tt) = idp
                  from-to (inr ((k , p) , ((j , g) , n))) = idp

  Frame-level : ∀ {n} (s-lvl : has-level (S n) I)
    → (a-lvl : {i : I} (f : Op P i) → has-level n (Arity P f))
    → {i : I} (w : W P i) (f : Op P i) → has-level n (Frame P w f)
  Frame-level s-lvl a-lvl w f = Π-level (λ j →
    ≃-level (n-type-right-cancel (Leaf-level a-lvl w) s-lvl j)
            (n-type-right-cancel (a-lvl f) s-lvl j))
