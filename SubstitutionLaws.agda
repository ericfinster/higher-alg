{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial

module SubstitutionLaws {ℓ} {I : Type ℓ} (P : Poly I) where

  open import Substitution P

  subst-graft : {i : I} (w : W P i) (ψ : ∀ j → Leaf P w j → W P j)
    → (κ : (g : Ops P) → Node P w g → Op Subst g)
    → (θ : (j : I) (l : Leaf P w j) (g : Ops P) → Node P (ψ j l) g → Op Subst g)
    -- Both elims turn out to be recs here ...
    → subst (graft P w ψ) (λ g → graft-node-elim P w ψ g (cst (Op Subst g)) (κ g) (λ j l n → θ j l g n)) ==
      graft P (subst w κ) (λ j → subst-lf-elim w κ j (cst (W P j)) (λ l → subst (ψ j l) (θ j l)))
  subst-graft (lf i) ψ κ θ = ! (subst-lf-elim-β (lf i) κ i (cst (W P i)) (λ l → subst (ψ i l) (θ i l)) idp)
  subst-graft {i} (nd (f , ϕ)) ψ κ θ =
    let (w , α) = κ (_ , f) (inl idp)
        p j l₀ = –> (α j) l₀
        ψ' j l₀ k l₁ = ψ k (j , p j l₀ , l₁)
        κ' j l₀ g n = κ g (inr (j , p j l₀ , n))
        θ' j l₀ k l₁ g n = θ k (j , p j l₀ , l₁) g n
        ψ₀ j l₀ = subst (ϕ j (p j l₀)) (κ' j l₀)
        ψ₁ k j l₀ l₁ = subst-lf-elim (ϕ j (p j l₀)) (κ' j l₀) k (cst (W P k)) (λ l₁ → subst (ψ' j l₀ k l₁) (θ' j l₀ k l₁)) l₁
    in graft P w (λ j l₀ → subst (graft P (ϕ j (p j l₀)) (ψ' j l₀))
                 (λ g → graft-node-elim P (ϕ j (p j l₀)) (ψ' j l₀) g (cst (Op Subst g)) (κ' j l₀ g) (λ k l₁ n → θ' j l₀ k l₁ g n)))
         =⟨ ap (graft P w) (λ= (λ j → (λ= (λ l₀ → subst-graft (ϕ j (p j l₀)) (ψ' j l₀) (κ' j l₀) (θ' j l₀))))) ⟩ -- By the induction hypothesis ...
       graft P w (λ j l₀ → graft P (subst (ϕ j (p j l₀)) (κ' j l₀)) (λ k → ψ₁ k j l₀))
         =⟨ ! (graft-assoc P w ψ₀ ψ₁) ⟩ -- By graft associativity ...
       graft P (graft P w ψ₀) (λ k → graft-leaf-rec P w ψ₀ k (ψ₁ k))
         =⟨ {!!} ⟩ -- By magic ? J.k. No, it should be a β-reduction for one of these elims ...
       graft P (graft P w ψ₀) (λ j → subst-lf-elim (nd (f , ϕ)) κ j (cst (W P j)) (λ l → subst (ψ j l) (θ j l))) ∎

  subst-unit : {i : I} (w : W P i)
    → subst w (λ g n → corolla P (snd g) , corolla-frm P (snd g)) == w
  subst-unit (lf i) = idp
  subst-unit (nd (f , ϕ)) = ap (λ x → nd (f , x))
    (λ= (λ j → λ= (λ p → subst-unit (ϕ j p))))

  subst-assoc : {i : I} (w : W P i)
    → (κ₀ : (g : Ops P) → Node P w g → Op Subst g)
    → (κ₁ : (h : Ops P) (n : Node P w h) (g : Ops P)
            → Node P (fst (κ₀ h n)) g → Op Subst g)
    → subst (subst w κ₀) (λ g → subst-nd-elim w κ₀ g (cst (Op Subst g)) (λ h n₀ n₁ → κ₁ h n₀ g n₁)) ==
      subst w (λ h n₀ → subst (fst (κ₀ h n₀)) (κ₁ h n₀) , λ j → (snd (κ₀ h n₀)) j ∘e subst-lf-eqv (fst (κ₀ h n₀)) (κ₁ h n₀) j)
  subst-assoc (lf i) κ₀ κ₁ = idp
  subst-assoc (nd (f , ϕ)) κ₀ κ₁ = {!!}

  -- Ah, okay, finally.  Now this is an application of the interchange
  -- between grafting an substitution ....

  -- Substitution and grafting commute

  -- Okay, yep.  First one is just a β redex on the leaf elim, I think.
  -- Second is graft associativity, induction hypothesis and some compatibility
  -- between graft nodes and subst leaves (which should be by definition).
  
