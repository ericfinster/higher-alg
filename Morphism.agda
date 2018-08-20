{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial

module Morphism where

  -- The approach based on functions seems to be considerably
  -- simpler when it comes to the functoriality of various
  -- constructions.  Let's keep going with it and see where we
  -- end up.

  -- This version of the notion of equivalence seems somehow easier
  -- to work with, as opposed to the one below.  But maybe not ...
  -- record PolyEqv {I J : Type₀} (P : Poly I) (Q : Poly J) : Type₀ where
  --   field
  --     ι≃ : I ≃ J
  --     γ≃ : (i : I) → γ P i ≃ γ Q (–> ι≃ i)
  --     ρ≃ : {i j : I} (c : γ P i) → ρ P c j ≃ ρ Q (–> (γ≃ i) c) (–> ι≃ j)

  record _→ₚ_ {I J : Type₀} (P : Poly I) (Q : Poly J) : Type₀ where
    field
      ι→ : I → J
      γ→ : {i : I} → γ P i → γ Q (ι→ i)
      ρ≃ : {i : I} (c : γ P i) {j : J}
        →  ρ Q (γ→ c) j ≃ Σ (hfiber ι→ j) (ρ P c ∘ fst)

    ρ←-typ : {i : I} (c : γ P i) {j : J}
      → ρ Q (γ→ c) j → I
    ρ←-typ c p = fst (fst (–> (ρ≃ c) p))

    ρ←-coh : {i : I} (c : γ P i) {j : J}
      → (p : ρ Q (γ→ c) j)
      → ι→ (ρ←-typ c p) == j
    ρ←-coh c p = snd (fst (–> (ρ≃ c) p))
    
    ρ← : {i : I} (c : γ P i) {j : J}
      → (p : ρ Q (γ→ c) j) → ρ P c (ρ←-typ c p)
    ρ← c p = snd (–> (ρ≃ c) p)

  -- Okay, you've had this idea about decorations.  Will it help
  -- with the kinds of proofs you have to do below?

  -- Functoriality of various constructions
  module _ {I J : Type₀} {P : Poly I} {Q : Poly J} (α : P →ₚ Q) where

    open _→ₚ_ α

    W→ : {i : I} → W P i → W Q (ι→ i)
    W→ (lf i) = lf (ι→ i)
    W→ (nd (c , δ)) = nd (γ→ c , λ j p → transport (W Q) (ρ←-coh c p) (W→ (δ _ (ρ← c p))) )

    W→-lf-to : {i : I} (w : W P i) (j : J)
      → Σ (hfiber ι→ j) (Leaf P w ∘ fst)
      → Leaf Q (W→ w) j
    W→-lf-to (lf .j) .(ι→ j) ((j , idp) , leaf .j) = leaf (ι→ j)
    W→-lf-to (nd (c , δ)) .(ι→ j) ((j , idp) , stem {j = k} p l) =
      stem p' (–> (lf-inv Q (snd (fst (fst (ρ≃ c) p')))
                  (W→ (δ (ρ←-typ c p') (snd (fst (ρ≃ c) p')))) (ι→ j))
                    (transport (λ x → Leaf Q (W→ (δ (fst x) (snd x))) (ι→ j))
                      (pair= (fst= (fst= (! coh))) (↓-ap-in _ _ (snd= (! coh)))) l'))

      where p' : ρ Q (γ→ c) (ι→ k)
            p' =  <– (ρ≃ c) ((k , idp) , p) 
            
            l' : Leaf Q (W→ (δ k p)) (ι→ j)
            l' = W→-lf-to (δ k p) (ι→ j) ((j , idp) , l)
  
            coh : –> (ρ≃ c) (<– (ρ≃ c) ((k , idp) , p)) == (k , idp) , p 
            coh = <–-inv-r (ρ≃ c) ((k , idp) , p)

    -- Ahhhhh!  Nightmare!!!!
    -- Somewhat surprising that this doesn't pass termination ...
    {-# TERMINATING #-}  
    W→-lf-from : {i : I} (w : W P i) (j : J)
      → Leaf Q (W→ w) j
      → Σ (hfiber ι→ j) (Leaf P w ∘ fst)
    W→-lf-from (lf i) .(ι→ i) (leaf .(ι→ i)) = (i , idp) , leaf i
    W→-lf-from (nd {i} (c , δ)) j (stem {j = k} p l) = fst ih , stem (snd pr) (snd ih)

      where pr : Σ (hfiber ι→ k) (ρ P c ∘ fst)
            pr = –> (ρ≃ c {k}) p
            
            w' : W P (fst (fst pr))
            w' = δ (fst (fst pr)) (snd pr)

            l' : Leaf Q (W→ w') j
            l' = <– (lf-inv Q (snd (fst (fst (ρ≃ c) p))) (W→ w') j) l

            ih : Σ (hfiber ι→ j) (Leaf P w' ∘ fst)
            ih = W→-lf-from w' j l'

    postulate
    
      W→-lf-to-from : {i : I} (w : W P i) (j : J)
        → (l : Leaf Q (W→ w) j)
        → W→-lf-to w j (W→-lf-from w j l) == l

      W→-lf-from-to : {i : I} (w : W P i) (j : J)
        → (l : Σ (hfiber ι→ j) (Leaf P w ∘ fst))
        → W→-lf-from w j (W→-lf-to w j l) == l

    W→-lf-eqv : {i : I} (w : W P i) (j : J)
      → Σ (hfiber ι→ j) (Leaf P w ∘ fst)
      ≃ Leaf Q (W→ w) j
    W→-lf-eqv w j = equiv (W→-lf-to w j) (W→-lf-from w j)
      (W→-lf-to-from w j) (W→-lf-from-to w j)

    -- Right, you'll probably have trouble with this computing
    -- later on ....
    Frame→ : {i : I} (w : W P i) (c : γ P i)
      → Frame P w c → Frame Q (W→ w) (γ→ c)
    Frame→ w c f j = (ρ≃ c {j})⁻¹ ∘e Σ-emap-r (f ∘ fst) ∘e (W→-lf-eqv w j)⁻¹

    -- Filling families are contravariant ...
    Family← : FillingFamily Q → FillingFamily P
    Family← F w c f = F (W→ w) (γ→ c) (Frame→ w c f)

    -- We need the same calculation for
    -- nodes in order to complete the map on filling polynomials

    ιγ→ : Σ I (γ P) → Σ J (γ Q)
    ιγ→ (i , c) = (ι→ i , γ→ c)
    
    W→-nd-to : {i : I} (w : W P i)
      → {j : J} (d : γ Q j) 
      → Σ (hfiber ιγ→ (j , d)) (λ hf → Node P w (snd (fst hf)))
      → Node Q (W→ w) d
    W→-nd-to (lf i) {j} d (_ , ())
    W→-nd-to (nd (c , δ)) .(γ→ d) (((j , d) , idp) , this) = this
    W→-nd-to (nd (c , δ)) .(γ→ d) (((j , d) , idp) , that {j = k} p n) = {!!}

    W→-nd-from : {i : I} (w : W P i)
      → {j : J} (d : γ Q j) 
      → Node Q (W→ w) d
      → Σ (hfiber ιγ→ (j , d)) (λ hf → Node P w (snd (fst hf)))
    W→-nd-from = {!!}

    postulate
    
      W→-nd-to-from : {i : I} (w : W P i)
        → {j : J} (d : γ Q j) 
        → (n : Node Q (W→ w) d)
        → W→-nd-to w d (W→-nd-from w d n) == n
        
      W→-nd-from-to : {i : I} (w : W P i)
        → {j : J} (d : γ Q j) 
        → (n : Σ (hfiber ιγ→ (j , d)) (λ hf → Node P w (snd (fst hf))))
        → W→-nd-from w d (W→-nd-to w d n) == n

    W→-nd-eqv : {i : I} (w : W P i)
      → {j : J} (d : γ Q j) 
      → Σ (hfiber ιγ→ (j , d)) (λ hf → Node P w (snd (fst hf)))
      ≃ Node Q (W→ w) d
    W→-nd-eqv w d = equiv (W→-nd-to w d) (W→-nd-from w d)
      (W→-nd-to-from w d) (W→-nd-from-to w d)
    
    //-fmap : (F : FillingFamily Q) → (P // Family← F) →ₚ (Q // F)
    _→ₚ_.ι→ (//-fmap F) = ιγ→ 
    _→ₚ_.γ→ (//-fmap F) (w , f , x) = W→ w , Frame→ w _ f , x
    _→ₚ_.ρ≃ (//-fmap F) (w , f , x) {j , d} = (W→-nd-eqv w d)⁻¹

  -- ... and hence so are domains
  {-# TERMINATING #-}
  Domain← : {I J : Type₀} {P : Poly I} {Q : Poly J}
    → P →ₚ Q → PolyDomain Q → PolyDomain P
  F (Domain← α D) = Family← α (F D)
  H (Domain← α D) = Domain← (//-fmap α (F D)) (H D)

  Extension : {I : Type₀} {P : Poly I} (F : FillingFamily P) → Type₁
  Extension {I} {P} F = {i : I} (w : W P i) (c : γ P i) (f : Frame P w c) (x : F w c f) → Type₀

  ExtendedFamily : {I : Type₀} {P : Poly I} (Fm : FillingFamily P)
    → (E : Extension Fm)
    → FillingFamily P
  ExtendedFamily Fm E w c f = Σ (Fm w c f) (E w c f)

  ExtendedPoly : {I : Type₀} {P : Poly I} (F : FillingFamily P)
    → (E : Extension F)
    → Poly (Σ I (γ P))
  γ (ExtendedPoly {P = P} F E) (i , c) = Σ (γ (P // F) (i , c)) (λ { (w , f , x) → E w c f x })
  ρ (ExtendedPoly {P = P} F E) (cc , _) = ρ (P // F) cc

  open _→ₚ_
  
  record _≃ₚ_ {I J : Type₀} (P : Poly I) (Q : Poly J) : Type₀ where
    constructor peq
    field
      morph : P →ₚ Q
      ι→-equiv : is-equiv (ι→ morph)
      γ→-equiv : {i : I} → is-equiv (γ→ morph {i})

  -- Right, and so we still need this statement, I think, but here
  -- is a nice version.
  thm : {I : Type₀} {P : Poly I} (F : FillingFamily P)
    → (E : Extension F)
    → (P // ExtendedFamily F E) ≃ₚ ExtendedPoly F E
  thm F E = {!!}

  -- Interesting.  So pulling back along morphisms in this representation
  -- is considerably easier.  Okay, so that seriously recommends this approach
  -- as opposed to the other one.

  -- So, can we construct the BD extension guy?

  -- BDExt : {I : Type₀} {P : Poly I} (F₀ : FillingFamily P) (F₁ : FillingFamily (P // F₀))
  --   → Poly (Σ (Σ I (γ P)) (γ (P // F₀)))
  -- γ (BDExt {P = P} F₀ F₁) ((i , c) , (w , f , x)) =
  --   Σ (γ ((P // F₀) // F₁) ((i , c) , (w , f , x))) (λ { (pd , ff , y) → {!(w , f , ff) == (flatten P pd , flatten-frm P pd , bd-frame P pd)!} })
  -- ρ (BDExt {P = P} F₀ F₁) (a , b) = ρ ((P // F₀) // F₁) a

  -- -- In short, yes, this is completely possible.

  -- BDMor : {I : Type₀} {P : Poly I} (F₀ : FillingFamily P) (F₁ : FillingFamily (P // F₀))
  --   → BDExt F₀ F₁ →ₚ ((P // F₀) // F₁)
  -- BDMor {P = P} F₀ F₁ = {!!}
 
  -- Okay, so I still think you are going to need a relation.  It's that, if you
  -- have an extension of a filling family, then you can slice over the sum of
  -- the family, or you can construct a polynomial over the slice.  And as before,
  -- you'll need to show that these two constructions give the same answer.

  -- The construction you give above is a special case.  And it's this form of
  -- naturality that lets you connect the whole string together at the base.

  -- -- Okey dokey.  And so what do we need to show about this?  Well, we'll
  -- -- need to be able to transfer domains across equivalences.

  -- module _ {I J : Type₀} {P : Poly I} {Q : Poly J} where

  --   poly-family-to : P ≃ₚ Q → FillingFamily P → FillingFamily Q
  --   poly-family-to (peq m α-eq β-eq) F w c f = {!!}


  -- poly-domain-to : {I J : Type₀} {P : Poly I} {Q : Poly J}
  --   → P ≃ₚ Q → PolyDomain P → PolyDomain Q
  -- F (poly-domain-to (peq f α-equiv β-equiv) D) = {!!}
  -- H (poly-domain-to (peq f α-equiv β-equiv) D) = {!poly-domain-to!}

  -- Yikes.  So there's a shitload of boilerplate.
  -- We have have to show that we can transform filling families
  -- across equivalences and so on and so forth....

  -- Oh holy shit.  It really goes down to everything. :(

  -- So since it looks like we will really have to write out
  -- functoriality and naturality of everything, maybe the morphism
  -- perspective is really better....