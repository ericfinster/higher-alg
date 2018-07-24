{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Poly
open import Util

module PolyMonad where

  CompositeFor : {I : Type₀} {P : Poly I} (F : FillingFamily P)
    → {i : I} (w : W P i) → Type₀
  CompositeFor {P = P} F {i} w = Σ (γ P i) (λ c → Σ (Frame P w c) (F w c))

  CoherenceFor : {I : Type₀} {P : Poly I} {F : FillingFamily P} (FF : FillingFamily (P // F))
    {i : I} {c : γ P i} (pd : W (P // F) (i , c)) → Type₀
  CoherenceFor {P = P} {F} FF {c = c} pd = Σ (F (flatten F pd) c (flatten-frm F pd))
    (λ f → FF pd (flatten F pd , flatten-frm F pd , f) (bd-frame F pd))

  CoherenceToComposite : {I : Type₀} {P : Poly I} {F : FillingFamily P} (FF : FillingFamily (P // F))
   {i : I} {c : γ P i} (pd : W (P // F) (i , c))
   → CoherenceFor FF pd → CompositeFor FF pd
  CoherenceToComposite {P = P} {F} FF pd (f₀ , f₁) =
    (flatten F pd , flatten-frm F pd , f₀) , bd-frame F pd , f₁

  --
  --  Polynomial Domains
  --
  
  record PolyDomain {I : Type₀} (P : Poly I) : Type₁ where
    coinductive
    field

      F : FillingFamily P 
      H : PolyDomain (P // F)

  open PolyDomain public

  record is-algebraic {I : Type₀} {P : Poly I} (D : PolyDomain P) : Type₁ where
    coinductive
    field

      is-fillable : {i : I} (w : W P i)
        → is-contr (CompositeFor (F D) w)

      is-coherent : {i : I} {c : γ P i} (pd : W (P // (F D)) (i , c))
        → is-equiv (CoherenceToComposite (F (H D)) pd)
        
      coh-algebraic : is-algebraic (H D)

  open is-algebraic public

  module _ {I : Type₀} {P : Poly I} (D : PolyDomain P) (is-alg : is-algebraic D) where

    bd-contr : {i : I} {c : γ P i} (tr : W (P // (F D)) (i , c))
      → is-contr (CoherenceFor (F (H D)) tr)
    bd-contr {c = c} pd = equiv-preserves-level ((CoherenceToComposite (F (H D)) pd , is-coherent is-alg pd)⁻¹)
      ⦃ is-fillable (coh-algebraic is-alg) pd ⦄

    μ : {i : I} (w : W P i) → γ P i
    μ w = fst (contr-center (is-fillable is-alg w))

    μ-frm : {i : I} (w : W P i) (j : I) → Leaf P w j ≃ ρ P (μ w) j
    μ-frm w = fst (snd (contr-center (is-fillable is-alg w)))

    μ-witness : {i : I} (w : W P i) → (F D) w (μ w) (μ-frm w)
    μ-witness w = snd (snd (contr-center (is-fillable is-alg w))) 

    η : (i : I) → γ P i
    η i = μ (lf i)

    ηρ-eqv : (i : I) (j : I) → Leaf P (lf i) j ≃ ρ P (η i) j
    ηρ-eqv i = μ-frm (lf i)

    ηρ-contr : (i : I) → is-contr (Σ I (ρ P (η i)))
    ηρ-contr i = equiv-preserves-level (Σ-emap-r (ηρ-eqv i)) ⦃ lf-lf-contr P i ⦄

    unit-r : (i : I) (c : γ P i) → μ (corolla P c) == c
    unit-r i c = fst= coh

      where ctr : W (P // F D) (i , c)
            ctr = lf (i , c)
            
            el : (F D) (corolla P c) c (corolla-lf-eqv P c)
            el = fst (contr-center (bd-contr ctr)) 

            hence : Σ (γ P i) (λ c₁ → Σ (Frame P (corolla P c) c₁) ((F D) (corolla P c) c₁))
            hence = c , corolla-lf-eqv P c , el

            coh : contr-center (is-fillable is-alg (corolla P c)) == hence
            coh = contr-path (is-fillable is-alg (corolla P c)) hence

      -- Uh, this one was pretty easy
      -- unit-l : (i : I) (w : W P i) → μ (graft P (lf i) (λ { j (leaf .j) → w })) == μ w
      -- unit-l i w = idp

  --   open module T = Substitution (F D)

  --   -- There's a different formulation which might be more intersting ...
  --   unit-l : (i : I) (w : W P i)
  --     → μ (nd (η i , λ j p → lf-elim P (λ j _ → W P j) w j (<– (μ-frm (lf i) j) p))) == μ w
  --   unit-l i w = {!!}

  --     where w' : W P i
  --           w' = nd (η i , λ j p → lf-elim P (λ j _ → W P j) w j (<– (μ-frm (lf i) j) p))

  --           dec : (j : Σ I (γ P)) → Node P w' (snd j) → W (P // F D) j
  --           dec (i , ._) (this ._ ._) = nd ((lf i , μ-frm (lf i) , μ-witness (lf i)) , λ { _ () })
  --           dec (i , c) (that ._ ._ p n) = lf (i , c) 

  --           ctr : W (P // F D) (i , μ w')
  --           ctr = nd ((w' , μ-frm w' , μ-witness w') , dec)

  --           el : F D (flatten-frm (μ w') ctr)
  --           el = fst (contr-center ((is-coherent is-alg) (μ w') ctr))

  --           -- So close ....
  --           -- hence : Σ (γ P i) (λ c₁ → Σ (Frame P {!!} c₁) (F D))
  --           -- hence = μ w' , flatten-frm (μ w') ctr , el


    -- -- Substituting a trivial decoration
    -- -- gives back the tree
    -- subst-lemma : {i : I} (w : W P i)
    --   → substitute (F D) w (λ ic n → lf ic) == w
    -- subst-lemma (lf i) = idp
    -- subst-lemma (nd {i} (c , δ)) =
    --   ap (λ x → nd (c , x))
    --      (λ= (λ j → λ= (λ p → subst-lemma (δ j p))))

    -- μ-hm : {i : I} (w : W P i) (ε : ∀ j → Leaf P w j → W P j)
    --   → μ (graft P w ε) == μ (nd (μ w , λ j p → ε j (<– (μ-frm w j) p )))
    -- μ-hm {i} w ε = {!!}

    --   where w' : W P i
    --         w' = nd (μ w , λ j p → ε j (<– (μ-frm w j) p ))

    --         dec : (j : Σ I (γ P)) → Node P w' (snd j) → W (P // F D) j
    --         dec (i , ._) this = nd ((w , μ-frm w , μ-witness w) , λ ic _ → lf ic)
    --         dec (i , c) (that p n) = lf (i , c)
            
    --         ctr : W (P // F D) (i , μ w')
    --         ctr = nd ((w' , μ-frm w' , μ-witness w') , dec)

    --         el : (F D) (flatten (F D) ctr) (μ w') (flatten-frm (F D) ctr)
    --         el = {!contr-center (bd-contr ctr) !} -- fst (contr-center (bd-contr ctr)) 

    --         -- As I expected, we need to prove an equation here saying that
    --         -- subsitution of a bunch of leaves gives back a tree
    --         hence : Σ (γ P i) (λ c₁ → Σ (Frame P (graft P w ε) c₁) (F D (graft P w ε) c₁))
    --         hence = μ w' , {!flatten-frm (F D) {c = μ w'} ctr!} , {!!} -- flatten-frm (F D) {c = μ w'} ctr , ?

    record unary-op (i j : I) : Type₀ where
      constructor uop
      field
        op : γ P j
        is-unary : is-contr (Σ I (ρ P op))
        dom : fst (contr-center is-unary) == i

    open unary-op

    comp-tr : ∀ {i j k} (u : unary-op i j) (v : unary-op j k) → W P k
    comp-tr (uop c is-u idp) (uop c' is-u' idp) =
      nd (c' , λ j p → corolla P (transport (γ P) (fst= (contr-path is-u' (j , p))) c)) 

    comp-tr-frm : ∀ {i j} (u : unary-op i j) (v : unary-op j i)
      → Frame P (comp-tr u v) (η i)
    comp-tr-frm u v = {!!}

    left-inverse : {i j : I} (u : unary-op i j) → Type₀
    left-inverse {i} {j} u = Σ (unary-op j i) (λ v → (F D) (comp-tr v u) (η j) (comp-tr-frm v u))

    right-inverse : {i j : I} (u : unary-op i j) → Type₀
    right-inverse {i} {j} u = Σ (unary-op j i) (λ v → (F D) (comp-tr u v) (η i) (comp-tr-frm u v))

    
