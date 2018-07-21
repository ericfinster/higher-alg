{-# OPTIONS --without-K --rewriting --type-in-type #-}

open import HoTT
open import Poly
open import Util

module PolyMonad where

  --
  --  Polynomial Domains
  --
  
  record PolyDomain {I : Type₀} (P : Poly I) : Type₁ where
    coinductive
    field

      F : {i : I} {w : W P i} {c : γ P i} → Frame P w c → Type₀
      H : PolyDomain (P // F)

  open PolyDomain public

  -- module _ {I : Type₀} {P : Poly I} (D : PolyDomain P) where

  --   open module S = Substitution (F D)
    
  --   bd-type : (i : I) (c : γ P i) (tr : W (P // (F D)) (i , c)) → Type₀
  --   bd-type i c tr = Σ ((F D) (flatten-frm c tr)) (λ f →
  --     F (H D) {c = (flatten c tr , flatten-frm c tr , f)} (λ jd → bd-frame c tr (snd jd))) 

  -- record is-algebraic {I : Type₀} {P : Poly I} (D : PolyDomain P) : Type₁ where
  --   coinductive
  --   field

  --     is-fillable : {i : I} (w : W P i) → is-contr (Σ (γ P i) (λ c → Σ (Frame P w c) (F D)))
  --     -- This should be replaced with the assetion that the type is non-empty.
  --     -- That it is contractible then follows from the fillability of higher dimensions
  --     is-coherent : {i : I} (c : γ P i) (tr : W (P // (F D)) (i , c)) → is-contr (bd-type D i c tr)
      
  --     coh-algebraic : is-algebraic (H D)

  -- open is-algebraic public

  --   -- Right, so it's slightly different in that we ask for the structure and the laws
  --   -- separately.  But it's a bit strange because it's not obviously the case any more
  --   -- that the "homs" are in fact monads.  So you would have to check this.  But at
  --   -- least this seems to avoid the difficulty from before.

  -- module _ {I : Type₀} {P : Poly I} (D : PolyDomain P) (is-alg : is-algebraic D) where

  --   μ : {i : I} (w : W P i) → γ P i
  --   μ w = fst (contr-center (is-fillable is-alg w))

  --   μ-frm : {i : I} (w : W P i) (j : I) → Leaf P w j ≃ ρ P (μ w) j
  --   μ-frm w = fst (snd (contr-center (is-fillable is-alg w)))
    
  --   μ-witness : {i : I} (w : W P i) → (F D) (μ-frm w)
  --   μ-witness w = snd (snd (contr-center (is-fillable is-alg w))) 

  --   η : (i : I) → γ P i
  --   η i = μ (lf i)

  --   ηρ-eqv : (i : I) (j : I) → Leaf P (lf i) j ≃ ρ P (η i) j
  --   ηρ-eqv i = μ-frm (lf i)
    
  --   ηρ-contr : (i : I) → is-contr (Σ I (ρ P (η i)))
  --   ηρ-contr i = equiv-preserves-level (Σ-emap-r (ηρ-eqv i)) ⦃ lf-lf-contr P i ⦄

  --   unit-r : (i : I) (c : γ P i) → μ (corolla P c) == c
  --   unit-r i c = fst= coh

  --     where ctr : W (P // F D) (i , c)
  --           ctr = lf (i , c)

  --           el : F D (λ j → corolla-lf-eqv P c j)
  --           el = fst (contr-center (is-coherent is-alg c ctr))

  --           hence : Σ (γ P i) (λ c₁ → Σ (Frame P (corolla P c) c₁) (F D))
  --           hence = c , corolla-lf-eqv P c , el

  --           coh : contr-center (is-fillable is-alg (corolla P c)) == hence
  --           coh = contr-path (is-fillable is-alg (corolla P c)) hence

  --   -- Uh, this one was pretty easy
  --   -- unit-l : (i : I) (w : W P i) → μ (graft P (lf i) (λ { j (leaf .j) → w })) == μ w
  --   -- unit-l i w = idp

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

  --   -- μ-hm : {i : I} (w : W P i) (ε : ∀ j → Leaf P w j → W P j)
  --   --   → μ (graft P w ε) == μ (nd (μ w , λ j p → ε j (<– (μ-frm w j) p )))
  --   -- μ-hm {i} w ε = {!!}

  --   --   where w' : W P i
  --   --         w' = nd (μ w , λ j p → ε j (<– (μ-frm w j) p ))

  --   --         dec : (j : Σ I (γ P)) → Node P w' (snd j) → W (P // F D) j
  --   --         dec (i , ._) (this ._ ._) = nd ((w , μ-frm w , μ-witness w) , λ ic _ → lf ic)
  --   --         dec (i , c) (that ._ ._ p n) = lf (i , c)
            
  --   --         ctr : W (P // F D) (i , μ w')
  --   --         ctr = nd ((w' , μ-frm w' , μ-witness w') , dec)

  --   --         el : F D (flatten-frm (μ w') ctr)
  --   --         el = fst (contr-center (has-coherences (fillers-coherent is-alg) (μ w') ctr))

  --   --         -- As I expected, we need to prove an equation here saying that
  --   --         -- subsitution of a bunch of leaves gives back a tree
  --   --         -- hence : Σ (γ P i) (λ c₁ → Σ (Frame P (graft P w ε) c₁) (F D))
  --   --         -- hence = μ w' , flatten-frm (μ w') ctr , el

  -- -- Yeah, so, uh, the interesting thing would be the universe.  So at this point, you
  -- -- need to rework the levels.  Oh, but okay, you can do type in type.

  -- 𝕌 : Poly ⊤
  -- γ 𝕌 unit = Type₀
  -- ρ 𝕌 X unit = X

  -- TermDomain : {I : Type₀} (P : Poly I) → PolyDomain P
  -- F (TermDomain P) = cst ⊤
  -- H (TermDomain P) = TermDomain (P // cst ⊤)

  -- -- What happens if we try to show the universe is a monad?
  -- 𝕌-Mnd : is-algebraic (TermDomain 𝕌)
  -- is-fillable 𝕌-Mnd w = has-level-in ((Leaf 𝕌 w unit , (λ { unit → ide (Leaf 𝕌 w tt) }) , unit) , λ { (X , e , unit) → {!!} })
  --   -- Exactly, and this is finished by univalence
  -- is-coherent 𝕌-Mnd = {!!}
  --   -- Here, you have to show it's non-empty, but this should be a lemma about
  --   -- grafting or whatever.  You construct it by induction.  
  -- coh-algebraic 𝕌-Mnd = {!!}

  --   -- And the final piece, this is a bit more tricky.  The only way I
  --   -- can see that would get you out is that for *any* coherent guy, it's
  --   -- double terminal guy is coherent.  Something like this.
