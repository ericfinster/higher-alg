{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Substitution

module PolyMonad where

  CompositeFor : ∀ {ℓ} {I : Type ℓ} {P : Poly I} (R : Relator P)
    → {i : I} (w : W P i) → Type ℓ
  CompositeFor {P = P} R {i} w = Σ (Op P i) (λ c → Σ (Frame P w c) (R w c))

  CoherenceFor : ∀ {ℓ} {I : Type ℓ} {P : Poly I} {R : Relator P} (RR : Relator (P // R))
    {i : I} {f : Op P i} (pd : W (P // R) (i , f)) → Type ℓ
  CoherenceFor {P = P} {R} RR {f = f} pd = Σ (R (flatten R pd) f (flatten-frm R pd))
    (λ f → RR pd (flatten R pd , flatten-frm R pd , f) (bd-frame R pd))

  coh-to-comp : ∀ {ℓ} {I : Type ℓ} {P : Poly I} {R : Relator P} (RR : Relator (P // R))
   {i : I} {f : Op P i} (pd : W (P // R) (i , f))
   → CoherenceFor RR pd → CompositeFor RR pd
  coh-to-comp {P = P} {R} RR pd (f₀ , f₁) =
    (flatten R pd , flatten-frm R pd , f₀) , bd-frame R pd , f₁

  Filler : ∀ {ℓ} {I : Type ℓ} {P : Poly I} (R : Relator P)
    → {i : I} (w : W P i) (c : Op P i) → Type ℓ
  Filler R w c = Σ (Frame _ w c) (R w c)

  filler-inv : ∀ {ℓ} {I : Type ℓ} {P : Poly I} (R : Relator P)
    → {i : I} {w₀ w₁ : W P i} (p : w₀ == w₁) (c : Op P i)
    → Filler R w₀ c ≃ Filler R w₁ c
  filler-inv R idp c = ide (Filler R _ c)

  record is-algebraic {ℓ} {I : Type ℓ} {P : Poly I} (D : Domain P) : Type (lsucc ℓ) where
    coinductive
    field

      is-fillable : {i : I} (w : W P i)
        → is-contr (CompositeFor (Rl D) w)

      is-coherent : {i : I} {f : Op P i} (pd : W (P // Rl D) (i , f))
        → is-equiv (coh-to-comp (Rl (Dm D)) pd)
        
      coh-algebraic : is-algebraic (Dm D)

  open is-algebraic public

  module _ {ℓ} {I : Type ℓ} {P : Poly I} (D : Domain P) (is-alg : is-algebraic D) where

    bd-contr : {i : I} {f : Op P i} (tr : W (P // Rl D) (i , f))
      → is-contr (CoherenceFor (Rl (Dm D)) tr)
    bd-contr pd = equiv-preserves-level ((coh-to-comp (Rl (Dm D)) pd , is-coherent is-alg pd)⁻¹)
      ⦃ is-fillable (coh-algebraic is-alg) pd ⦄

    μ : {i : I} (w : W P i) → Op P i
    μ w = fst (contr-center (is-fillable is-alg w))

    μ-frm : {i : I} (w : W P i) (j : I) → Leaf P w j ≃ Param P (μ w) j
    μ-frm w = fst (snd (contr-center (is-fillable is-alg w)))

    μ-witness : {i : I} (w : W P i) → (Rl D) w (μ w) (μ-frm w)
    μ-witness w = snd (snd (contr-center (is-fillable is-alg w))) 

    η : (i : I) → Op P i
    η i = μ (lf i)

    ηρ-eqv : (i : I) (j : I) → Leaf P (lf i) j ≃ Param P (η i) j
    ηρ-eqv i = μ-frm (lf i)

    -- ηρ-contr : (i : I) → is-contr (Σ I (Param P (η i)))
    -- ηρ-contr i = equiv-preserves-level (Σ-emap-r (ηρ-eqv i)) ⦃ lf-lf-contr P i ⦄

    unit-r : (i : I) (f : Op P i) → μ (corolla P f) == f
    unit-r i f = fst= coh

      where ctr : W (P // Rl D) (i , f)
            ctr = lf (i , f)
            
            el : (Rl D) (corolla P f) f (flatten-frm (Rl D) ctr)
            el = fst (contr-center (bd-contr ctr)) 

            hence : Σ (Op P i) (λ f₁ → Σ (Frame P (corolla P f) f₁) ((Rl D) (corolla P f) f₁))
            hence = f , flatten-frm (Rl D) ctr , el 

            coh : contr-center (is-fillable is-alg (corolla P f)) == hence
            coh = contr-path (is-fillable is-alg (corolla P f)) hence

    -- Substituting a trivial decoration
    -- gives back the tree
    subst-lemma : {i : I} (w : W P i)
      → substitute (Rl D) w (λ ic n → lf ic) == w
    subst-lemma (lf i) = idp
    subst-lemma (nd {i} (c , δ)) =
      ap (λ x → nd (c , x))
         (λ= (λ j → λ= (λ p → subst-lemma (δ j p))))

    -- The previous lemma is compatible with grafting ...
    subst-graft-lemma : {i : I} (w : W P i)
      → (ε : ∀ j → Leaf P w j → W P j)
      → graft P (substitute (Rl D) w (λ ic _ → lf ic))
              (λ j l → substitute (Rl D) (ε j (substitute-lf-to (Rl D) w (λ ic _ → lf ic) j l)) (λ ic _ → lf ic))
        == graft P w ε
    subst-graft-lemma (lf i) ε = subst-lemma (ε i idp)
    subst-graft-lemma (nd (c , δ)) ε = ap (λ d → nd (c , d)) (λ= (λ j → λ= (λ p → subst-graft-lemma (δ j p) (λ k l → ε k (j , p , l))))) 
  
    μ-hm : {i : I} (w : W P i) (ε : ∀ j → Leaf P w j → W P j)
      → μ (graft P w ε) == μ (nd (μ w , λ j p → ε j (<– (μ-frm w j) p )))
    μ-hm {i} w ε = fst= coh

      where w' : W P i
            w' = nd (μ w , λ j p → ε j (<– (μ-frm w j) p ))

            dec : (j : Σ I (Op P)) → Node P w' (snd j) → W (P // Rl D) j
            dec (i , ._) (inl idp) = nd ((w , μ-frm w , μ-witness w) , λ ic _ → lf ic)
            dec (i , f) (inr (j , p , n)) = lf (i , f)
            
            ctr : W (P // Rl D) (i , μ w')
            ctr = nd ((w' , μ-frm w' , μ-witness w') , dec)

            claim : flatten (Rl D) ctr == graft P w ε
            claim = ap (λ e → graft P (substitute (Rl D) w (λ ic _ → lf ic)) e)
                       (λ= (λ j → λ= (λ l → ap (λ x → substitute (Rl D) (ε j x) (λ ic _ → lf ic))
                                               (<–-inv-l (μ-frm w j) (substitute-lf-to (Rl D) w (λ ic _ → lf ic) j l))))) ∙ subst-graft-lemma w ε

            el : (Rl D) (flatten (Rl D) ctr) (μ w') (flatten-frm (Rl D) ctr)
            el = fst (contr-center (bd-contr ctr))

            hence : Σ (Op P i) (λ c₁ → Σ (Frame P (graft P w ε) c₁) (Rl D (graft P w ε) c₁))
            hence = μ w' , –> (filler-inv (Rl D) claim (μ w')) (flatten-frm (Rl D) ctr , fst (contr-center (bd-contr ctr)))

            coh : contr-center (is-fillable is-alg (graft P w ε)) == hence
            coh = contr-path (is-fillable is-alg (graft P w ε)) hence

    -- An immediate consequence of the previous should
    -- be the left unit law:
    unit-l : (i : I) (w : W P i)
      → μ w == μ (nd (η i , λ j p → transport (W P) (<– (μ-frm (lf i) j) p) w)) 
    unit-l i w = μ-hm (lf i) (λ j l → transport (W P) l w)
    
    record unary-op (i j : I) : Type ℓ where
      constructor uop
      field
        op : Op P j
        is-unary : is-contr (Σ I (Param P op))
        dom : fst (contr-center is-unary) == i

    open unary-op

    unary-dec : (X : I → Type ℓ)
      → {i j : I} (u : unary-op i j)
      → X i → ∀ k → Param P (op u) k → X k
    unary-dec X (uop c is-u idp) x k p = transport X (fst= (contr-path is-u (k , p))) x

    extend : ∀ {i j} (u : unary-op i j) → W P i → W P j
    extend u w = nd (op u , unary-dec (W P) u w)
            
    extend-lf-to : ∀ {i j} (u : unary-op i j) (w : W P i)
      → ∀ k → Leaf P (extend u w) k → Leaf P w k
    extend-lf-to (uop c is-u idp) w k (j , p , l) =
      <– (lf-inv P (fst= (contr-path is-u (j , p))) w k) l

    extend-lf-from : ∀ {i j} (u : unary-op i j) (w : W P i)
      → ∀ k → Leaf P w k → Leaf P (extend u w) k
    extend-lf-from (uop c is-u idp) w k l =
      let p = snd (contr-center is-u)
          pth = fst= (contr-path is-u (contr-center is-u))
      in (_ , p , –> (lf-inv P pth w k) l)

    postulate
    
      extend-lf-to-from : ∀ {i j} (u : unary-op i j) (w : W P i)
        → ∀ k → (l : Leaf P w k)
        → extend-lf-to u w k (extend-lf-from u w k l) == l

      extend-lf-from-to : ∀ {i j} (u : unary-op i j) (w : W P i)
        → ∀ k → (l : Leaf P (extend u w) k)
        → extend-lf-from u w k (extend-lf-to u w k l) == l

    extend-lf-eqv : ∀ {i j} (u : unary-op i j) (w : W P i)
      → ∀ k → Leaf P (extend u w) k ≃ Leaf P w k
    extend-lf-eqv u w k = equiv (extend-lf-to u w k) (extend-lf-from u w k)
      (extend-lf-to-from u w k) (extend-lf-from-to u w k)

    comp-tr : ∀ {i j k} (u : unary-op i j) (v : unary-op j k) → W P k
    comp-tr u v = extend v (corolla P (op u)) 

    -- -- Yikes.  What a nightmare.  You'll have to simplify this.
    -- comp-tr-frm : ∀ {i j} (u : unary-op i j) (v : unary-op j i)
    --   → Frame P (comp-tr u v) (η i)
    -- comp-tr-frm {i} u v k =
    --   μ-frm (lf i) k ∘e
    --   {!!} ∘e
    --   corolla-lf-eqv P (op u) k ∘e
    --   extend-lf-eqv v (corolla P (op u)) k

    -- left-inverse : {i j : I} (u : unary-op i j) → Type ℓ
    -- left-inverse {i} {j} u = Σ (unary-op j i) (λ v → (Rl D) (comp-tr v u) (η j) (comp-tr-frm v u))

    -- right-inverse : {i j : I} (u : unary-op i j) → Type ℓ
    -- right-inverse {i} {j} u = Σ (unary-op j i) (λ v → (Rl D) (comp-tr u v) (η i) (comp-tr-frm u v))

    
