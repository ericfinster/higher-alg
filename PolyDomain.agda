{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Poly

module PolyDomain where

  Frame : {I : Type₀} (P : Poly I) {i : I} (w : W P i) (c : γ P i) → Type₀
  Frame {I} P w c = (j : I) → Leaf P w j ≃ ρ P c j

  FillingFamily : {I : Type₀} → Poly I → Type₁
  FillingFamily {I} P = {i : I} {w : W P i} {c : γ P i} → Frame P w c → Type₀

  _//_ : {I : Type₀} (P : Poly I) (F : FillingFamily P) → Poly (Σ I (γ P))
  γ (P // F) (i , c) = Σ (W P i) (λ w → Σ (Frame P w c) F)
  ρ (P // F) (w , f , x) (j , d) = Node P w d

  --
  --  The Baez-Dolan substitution operation
  --

  module Substitution {I : Type₀} {P : Poly I} (F : FillingFamily P) where

    {-# TERMINATING #-}
    flatten : {i : I} (c : γ P i)
      → (tr : W (P // F) (i , c))
      → W P i

    -- The flattened tree has a canonical c-frame
    flatten-frm : {i : I} (c : γ P i)
      → (tr : W (P // F) (i , c))
      → (j : I) → Leaf P (flatten c tr) j ≃ ρ P c j

    substitute : {i : I} (w : W P i)
      → (κ : (c : Σ I (γ P)) → Node P w (snd c) → W (P // F) c)
      → W P i

    -- A substituted tree has the same leaves
    substitute-lf-eqv : {i : I} (w : W P i)
      → (κ : (c : Σ I (γ P)) → Node P w (snd c) → W (P // F) c)
      → (j : I) → Leaf P (substitute w κ) j ≃ Leaf P w j

    flatten c (lf .(_ , c)) = corolla P c
    flatten c (nd ((w , f , x) , ε)) = substitute w ε

    flatten-frm c (lf .(_ , c)) j = corolla-lf-eqv P c j
    flatten-frm c (nd ((w , f , x) , ε)) j = f j ∘e substitute-lf-eqv w ε j

    substitute (lf i) κ = lf i
    substitute (nd {i} (c , δ)) κ =
      let tr = κ (i , c) (this c δ)
          p j l = –> (flatten-frm c tr j) l
          ε j l = substitute (δ j (p j l)) (λ ic n → κ ic (that c δ (p j l) n))
      in graft P (flatten c tr) ε 

    substitute-lf-eqv (lf i) κ j = ide (Leaf P (lf i) j)
    substitute-lf-eqv (nd {i} (c , δ)) κ j =
      let tr = κ (i , c) (this c δ)
          p j l = –> (flatten-frm c tr j) l
          κ' j l ic n = κ ic (that c δ (p j l) n)
          ε j l = substitute (δ j (p j l)) (κ' j l) 
      in nd-lf-eqv P c δ j ∘e
         Σ-emap-r (λ k → Σ-emap-l (λ p → Leaf P (δ k p) j) (flatten-frm c tr k) ∘e
                         Σ-emap-r (λ l → substitute-lf-eqv (δ k (p k l)) (κ' k l) j)) ∘e
         graft-leaf-eqv P (flatten c tr) ε j

    postulate

      bd-frame : {i : I} (c : γ P i)
        → (tr : W (P // F) (i , c))
        → {j : I} (d : γ P j)
        → Leaf (P // F) tr (j , d) ≃ Node P (flatten c tr) d

  --
  --  Polynomial Domains
  --
  
  record PolyDomain {I : Type₀} (P : Poly I) : Type₁ where
    coinductive
    field

      F : {i : I} {w : W P i} {c : γ P i} → Frame P w c → Type₀
      H : PolyDomain (P // F)

  open PolyDomain public

  module _ {I : Type₀} {P : Poly I} (D : PolyDomain P) where

    open module S = Substitution (F D)
    
    bd-type : (i : I) (c : γ P i) (tr : W (P // (F D)) (i , c)) → Type₀
    bd-type i c tr = Σ ((F D) (flatten-frm c tr)) (λ f → F (H D) {w = tr} {c = (flatten c tr , flatten-frm c tr , f)} (λ jd → bd-frame c tr (snd jd))) 

    -- Okay, good.  So the second thing I'm being asked is what I still haven't proved:
    -- that nodes of the Baez-Dolan substitute are the same as the leaves of the filling
    -- tree.  And in this case, this is a well defined type.
    
    -- Phew.  Okay.  And now the axiom is that, for any pasting diagram, the set of such
    -- pairs is contractible.  This *enforces by typing* that the composites of coherences
    -- have the correct shape.

    -- Yeah, so this is a real problem.  I don't at all see how to prove the slice is
    -- again a monad.  So, the idea is that we advance the definition by 1 to make it
    -- truly coinductive.

  record is-algebraic {I : Type₀} {P : Poly I} (D : PolyDomain P) : Type₁ where
    coinductive
    field

      is-fillable : {i : I} (w : W P i) → is-contr (Σ (γ P i) (λ c → Σ (Frame P w c) (F D)))
      is-coherent : {i : I} (c : γ P i) (tr : W (P // (F D)) (i , c)) → is-contr (bd-type D i c tr)
      
      coh-algebraic : is-algebraic (H D)

  open is-algebraic public

    -- Right, so it's slightly different in that we ask for the structure and the laws
    -- separately.  But it's a bit strange because it's not obviously the case any more
    -- that the "homs" are in fact monads.  So you would have to check this.  But at
    -- least this seems to avoid the difficulty from before.

  module _ {I : Type₀} {P : Poly I} (D : PolyDomain P) (is-alg : is-algebraic D) where

    μ : {i : I} (w : W P i) → γ P i
    μ w = fst (contr-center (is-fillable is-alg w))

    μ-frm : {i : I} (w : W P i) (j : I) → Leaf P w j ≃ ρ P (μ w) j
    μ-frm w = fst (snd (contr-center (is-fillable is-alg w)))
    
    μ-witness : {i : I} (w : W P i) → (F D) (μ-frm w)
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

            el : F D (λ j → corolla-lf-eqv P c j)
            el = fst (contr-center (is-coherent is-alg c ctr))

            hence : Σ (γ P i) (λ c₁ → Σ (Frame P (corolla P c) c₁) (F D))
            hence = c , corolla-lf-eqv P c , el

            coh : contr-center (is-fillable is-alg (corolla P c)) == hence
            coh = contr-path (is-fillable is-alg (corolla P c)) hence

    -- Uh, this one was pretty easy
    unit-l : (i : I) (w : W P i) → μ (graft P (lf i) (λ { j (leaf .j) → w })) == μ w
    unit-l i w = idp

    -- There's a different formulation which might be more intersting ...
    -- unit-l : (i : I) (w : W P i)
    --   → μ (nd (η i , λ j → {!μ-frm (lf i) j!})) == μ w
    -- unit-l i w = {!!}

    -- open module T = Substitution (F D)

    -- μ-hm : {i : I} (w : W P i) (ε : ∀ j → Leaf P w j → W P j)
    --   → μ (graft P w ε) == μ (nd (μ w , λ j p → ε j (<– (μ-frm w j) p )))
    -- μ-hm {i} w ε = {!!}

    --   where w' : W P i
    --         w' = nd (μ w , λ j p → ε j (<– (μ-frm w j) p ))

    --         dec : (j : Σ I (γ P)) → Node P w' (snd j) → W (P // F D) j
    --         dec (i , ._) (this ._ ._) = nd ((w , μ-frm w , μ-witness w) , λ ic _ → lf ic)
    --         dec (i , c) (that ._ ._ p n) = lf (i , c)
            
    --         ctr : W (P // F D) (i , μ w')
    --         ctr = nd ((w' , μ-frm w' , μ-witness w') , dec)

    --         el : F D (flatten-frm (μ w') ctr)
    --         el = fst (contr-center (has-coherences (fillers-coherent is-alg) (μ w') ctr))

    --         -- As I expected, we need to prove an equation here saying that
    --         -- subsitution of a bunch of leaves gives back a tree
    --         -- hence : Σ (γ P i) (λ c₁ → Σ (Frame P (graft P w ε) c₁) (F D))
    --         -- hence = μ w' , flatten-frm (μ w') ctr , el




