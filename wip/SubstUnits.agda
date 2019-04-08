open import HoTT
open import Util
open import Polynomial

-- Proving that substitution is associative
module wip.SubstUnits {ℓ} {I : Type ℓ} (P : Poly I) where

  open import Grafting P
  open import Substitution P

  subst-η : (f : Ops P) → InFrame P f
  subst-η (_ , f) = corolla P f , corolla-frm P f

  subst-η-dec : {i : I} (w : W P i) →
    (g : Ops P) (n : Node P w g) → InFrame P g
  subst-η-dec w g n = subst-η g

  subst-η-frm : (f g : Ops P)
    → (f == g) ≃ (f == g) ⊔ Σ I (λ k → Σ (Param P (snd f) k) (λ p → Lift {j = ℓ} ⊥))
  subst-η-frm f g = equiv inl from to-from (λ _ → idp)

    where from : (f == g) ⊔ Σ I (λ k → Σ (Param P (snd f) k) (λ p → Lift ⊥)) → f == g
          from (inl e) = e
          from (inr (_ , _ , ()))

          to-from : (e : (f == g) ⊔ Σ I (λ k → Σ (Param P (snd f) k) (λ p → Lift ⊥)))
            → inl (from e) == e
          to-from (inl e) = idp
          to-from (inr (_ , _ , ()))

  --
  --  Unit left law
  --

  subst-unit-l : {i : I} (w : W P i)
    →  subst w (subst-η-dec w) == w
  subst-unit-l (lf i) = idp
  subst-unit-l (nd (f , ϕ)) = ap (λ x → nd (f , x))
    (Decor-== P (λ j p → subst-unit-l (ϕ j p)))

  subst-unit-l-lem : {i : I} (w : W P i)
    → (j : I) (l : Leaf P (subst w (subst-η-dec w)) j)
    → l == subst-leaf-from w (subst-η-dec w) j l [ (λ x → Leaf P x j) ↓ subst-unit-l w ]
  subst-unit-l-lem (lf i) j l = idp
  subst-unit-l-lem (nd (f , ϕ)) j (k , p , l) =
    ↓-ap-in (λ x → Leaf P x j)
            (λ x → nd (f , x))
            (↓-nd-Leaf-ih P (λ j₁ p₁ → subst-unit-l (ϕ j₁ p₁)) k p
                            (subst-unit-l-lem (ϕ k p) j l))

  subst-unit-l-frm : {i : I} {f : Op P i}
    → (w : W P i) (α : Frame P w f)
    → (λ j → α j ∘e (subst-leaf-eqv w (λ g n → subst-η g) j) ⁻¹)
        == α [ (λ x → Frame P x f) ↓ subst-unit-l w ]
  subst-unit-l-frm w α =
    let lem j l₀ l₁ q = –> (α j) (subst-leaf-from w (subst-η-dec w) j l₀)
                          =⟨ ! (to-transp (subst-unit-l-lem w j l₀)) |in-ctx (–> (α j)) ⟩
                        –> (α j) (transport (λ x → Leaf P x j) (subst-unit-l w) l₀)
                          =⟨ to-transp q |in-ctx (–> (α j)) ⟩ 
                        –> (α j) l₁ ∎
    in ↓-W-Frame-in P lem

  subst-node-unit-l : {i : I} (w : W P i)
    → (g : Ops P) (n : Node P w g)
    → subst-node-to w (subst-η-dec w) g (g , n , inl idp)
      == n [ (λ x → Node P x g) ↓ subst-unit-l w ]
  subst-node-unit-l (lf i) g (lift ())
  subst-node-unit-l (nd (f , ϕ)) ._ (inl idp) =
    ↓-ap-in (λ x → Node P x (_ , f)) (λ x → nd (f , x))
      (↓-Node-here-in P (Decor-== P (λ j p → subst-unit-l (ϕ j p))))
  subst-node-unit-l (nd (f , ϕ)) g (inr (k , p , n)) =
    ↓-ap-in (λ x → Node P x g) (λ x → nd (f , x))
      (↓-Node-there-in P (λ j p₁ → subst-unit-l (ϕ j p₁)) k p
        (subst-node-unit-l (ϕ k p) g n))

  --
  --  Unit right law
  -- 

  subst-unit-r-lem : {i : I} (w : W P i)
    → (j : I) (t : Σ I (λ k → Σ (Leaf P w k) (λ l → k == j)))
    → graft-unit-lf-to w j (graft-leaf-to w (λ k _ → lf k) j t)
      == transport (Leaf P w) (snd (snd t)) (fst (snd t))
  subst-unit-r-lem (lf i) .i (.i , idp , idp) = idp
  subst-unit-r-lem (nd (f , ϕ)) j (.j , (k , p , l) , idp) =
    ap (λ x → (k , p , x)) (subst-unit-r-lem (ϕ k p) j (j , l , idp))

  subst-unit-r-frm : {i : I} {f : Op P i}
    → (κ : (g : Ops P) → Node P (corolla P f) g → InFrame P g)
    → snd (κ (i , f) (inl idp))
        == (λ j → corolla-frm P f j ∘e (subst-leaf-eqv (corolla P f) κ j) ⁻¹)
             [ (λ x → Frame P x f) ↓ graft-unit (fst (κ (i , f) (inl idp))) ]
  subst-unit-r-frm {i} {f} κ = 
    let (w , α) = κ (i , f) (inl idp)
        ψ k _ = lf k
        t j l = graft-leaf-from w ψ j l
        
        lem j l = –> (α j) (graft-unit-lf-to w j l)
                    =⟨ ! (graft-leaf-to-from w ψ j l) |in-ctx (λ x → –> (α j) (graft-unit-lf-to w j x)) ⟩
                  –> (α j) (graft-unit-lf-to w j (graft-leaf-to w ψ j (t j l)))
                    =⟨ subst-unit-r-lem w j (t j l) |in-ctx (–> (α j)) ⟩
                  –> (α j) (transport (Leaf P w) (snd (snd (t j l))) (fst (snd (t j l))))
                    =⟨ transp-→ (Leaf P w) (Param P f) (snd (snd (t j l))) (λ i → –> (α i)) ⟩ 
                  –> (corolla-frm P f j) (subst-leaf-from (corolla P f) κ j l) ∎

    in graft-unit-frm w α ∙'ᵈ (λ= λ j → equiv-== (λ l → lem j l))

