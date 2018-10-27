{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Substitution

module Morphism where

  record _→ₚ_ {ℓ} {I J : Type ℓ} (P : Poly I) (Q : Poly J) : Type ℓ where
    field
      Sort→ : I → J
      Op→ : {i : I} → Op P i → Op Q (Sort→ i)
      Param≃ : {i : I} (f : Op P i) {j : J}
        →  Param Q (Op→ f) j ≃ Σ (hfiber Sort→ j) (Param P f ∘ fst)

    Param←-typ : {i : I} (f : Op P i) {j : J}
      → Param Q (Op→ f) j → I
    Param←-typ f p = fst (fst (–> (Param≃ f) p))

    Param←-coh : {i : I} (f : Op P i) {j : J}
      → (p : Param Q (Op→ f) j)
      → Sort→ (Param←-typ f p) == j
    Param←-coh f p = snd (fst (–> (Param≃ f) p))
    
    Param← : {i : I} (f : Op P i) {j : J}
      → (p : Param Q (Op→ f) j) → Param P f (Param←-typ f p)
    Param← f p = snd (–> (Param≃ f) p)

  -- Functoriality of various constructions
  module _ {ℓ} {I J : Type ℓ} {P : Poly I} {Q : Poly J} (α : P →ₚ Q) where

    open _→ₚ_ α

    W→ : {i : I} → W P i → W Q (Sort→ i)
    W→ (lf i) = lf (Sort→ i)
    W→ (nd (f , ϕ)) = nd (Op→ f , λ j p → transport (W Q) (Param←-coh f p) (W→ (ϕ _ (Param← f p))) )

    -- Ahhhhh!  Nightmare!!!!
    -- Somewhat surprising that this doesn't pass termination ...
    -- Probably you need an auxillary function which calculates the
    -- first component (the hfiber) so that agda sees it is done recursively ...
    {-# TERMINATING #-}  
    W→-lf-to : {i : I} (w : W P i) (j : J)
      → Leaf Q (W→ w) j
      → Σ (hfiber Sort→ j) (Leaf P w ∘ fst)
    W→-lf-to (lf i) .(Sort→ i) idp = (i , idp) , idp
    W→-lf-to (nd {i} (f , ϕ)) j (k , p , l) = fst ih , fst (fst pr) , snd pr , snd ih

      where pr : Σ (hfiber Sort→ k) (Param P f ∘ fst)
            pr = –> (Param≃ f {k}) p
            
            w' : W P (fst (fst pr))
            w' = ϕ (fst (fst pr)) (snd pr)

            l' : Leaf Q (W→ w') j
            l' = <– (lf-inv Q (snd (fst (fst (Param≃ f) p))) (W→ w') j) l

            ih : Σ (hfiber Sort→ j) (Leaf P w' ∘ fst)
            ih = W→-lf-to w' j l'

    W→-lf-from : {i : I} (w : W P i) (j : J)
      → Σ (hfiber Sort→ j) (Leaf P w ∘ fst)
      → Leaf Q (W→ w) j
    W→-lf-from (lf .j) .(Sort→ j) ((j , idp) , idp) = idp
    W→-lf-from (nd (f , ϕ)) .(Sort→ j) ((j , idp) , (k , p , l)) =
      Sort→ k , p' , (–> (lf-inv Q (snd (fst (fst (Param≃ f) p')))
                         (W→ (ϕ (Param←-typ f p') (snd (fst (Param≃ f) p')))) (Sort→ j))
                           (transport (λ x → Leaf Q (W→ (ϕ (fst x) (snd x))) (Sort→ j))
                             (pair= (fst= (fst= (! coh))) (↓-ap-in _ _ (snd= (! coh)))) l'))

      where p' : Param Q (Op→ f) (Sort→ k)
            p' =  <– (Param≃ f) ((k , idp) , p) 
            
            l' : Leaf Q (W→ (ϕ k p)) (Sort→ j)
            l' = W→-lf-from (ϕ k p) (Sort→ j) ((j , idp) , l)
  
            coh : –> (Param≃ f) (<– (Param≃ f) ((k , idp) , p)) == (k , idp) , p 
            coh = <–-inv-r (Param≃ f) ((k , idp) , p)

    postulate
    
      W→-lf-to-from : {i : I} (w : W P i) (j : J)
        → (l : Σ (hfiber Sort→ j) (Leaf P w ∘ fst))
        → W→-lf-to w j (W→-lf-from w j l) == l

      W→-lf-from-to : {i : I} (w : W P i) (j : J)
        → (l : Leaf Q (W→ w) j)
        → W→-lf-from w j (W→-lf-to w j l) == l

    W→-lf-eqv : {i : I} (w : W P i) (j : J)
      → Leaf Q (W→ w) j
      ≃ Σ (hfiber Sort→ j) (Leaf P w ∘ fst)
    W→-lf-eqv w j = equiv (W→-lf-to w j) (W→-lf-from w j)
      (W→-lf-to-from w j) (W→-lf-from-to w j)

    SortOp→ : Σ I (Op P) → Σ J (Op Q)
    SortOp→ (i , c) = (Sort→ i , Op→ c)

    -- Here we use exactly the same style of argument as for the leaves.
    -- Probably you should be able to abstract this so that it is more
    -- easily useable in the future....

    {-# TERMINATING #-}  
    W→-nd-to : {i : I} (w : W P i)
      → {j : J} (d : Op Q j) 
      → Node Q (W→ w) d
      → Σ (hfiber SortOp→ (j , d)) (λ hf → Node P w (snd (fst hf)))
    W→-nd-to (lf i) d ()
    W→-nd-to (nd {i} (f , ϕ)) .(Op→ f) (inl idp) = ((i , f) , idp) , inl idp
    W→-nd-to (nd (f , ϕ)) {j} d (inr (k , p , n)) = fst ih , (inr (fst (fst pr) , snd pr , snd ih))

      where pr : Σ (hfiber Sort→ k) (Param P f ∘ fst)
            pr = –> (Param≃ f {k}) p
            
            w' : W P (fst (fst pr))
            w' = ϕ (fst (fst pr)) (snd pr)

            n' : Node Q (W→ w') d
            n' = <– (nd-inv Q (snd (fst (fst (Param≃ f) p))) (W→ w') d) n

            ih : Σ (hfiber SortOp→ (j , d)) (λ hf → Node P w' (snd (fst hf))) 
            ih = W→-nd-to w' d n' 

    W→-nd-from : {i : I} (w : W P i)
      → {j : J} (d : Op Q j) 
      → Σ (hfiber SortOp→ (j , d)) (λ hf → Node P w (snd (fst hf)))
      → Node Q (W→ w) d
    W→-nd-from (lf i) {j} d (_ , ())
    W→-nd-from (nd (f , ϕ)) .(Op→ d) (((j , d) , idp) , inl idp) = inl idp
    W→-nd-from (nd (f , ϕ)) .(Op→ d) (((j , d) , idp) , inr (k , p , n)) =
      inr (Sort→ k ,  p' ,
        (–> (nd-inv Q (snd (fst (fst (Param≃ f) p'))) (W→ (ϕ (Param←-typ f p') (snd (fst (Param≃ f) p')))) (Op→ d))
          (transport (λ x → Node Q (W→ (ϕ (fst x) (snd x))) (Op→ d))
            (pair= (fst= (fst= (! coh))) (↓-ap-in _ _ (snd= (! coh)))) n')))

      where p' : Param Q (Op→ f) (Sort→ k)
            p' =  <– (Param≃ f) ((k , idp) , p) 

            n' : Node Q (W→ (ϕ k p)) (Op→ d)
            n' = W→-nd-from (ϕ k p) (Op→ d) (((j , d) , idp) , n)
  
            coh : –> (Param≃ f) (<– (Param≃ f) ((k , idp) , p)) == (k , idp) , p 
            coh = <–-inv-r (Param≃ f) ((k , idp) , p)

    postulate
    
      W→-nd-to-from : {i : I} (w : W P i)
        → {j : J} (d : Op Q j) 
        → (n : Σ (hfiber SortOp→ (j , d)) (λ hf → Node P w (snd (fst hf))))
        → W→-nd-to w d (W→-nd-from w d n) == n
        
      W→-nd-from-to : {i : I} (w : W P i)
        → {j : J} (d : Op Q j) 
        → (n : Node Q (W→ w) d)
        → W→-nd-from w d (W→-nd-to w d n) == n

    W→-nd-eqv : {i : I} (w : W P i)
      → {j : J} (d : Op Q j) 
      → Node Q (W→ w) d
      ≃ Σ (hfiber SortOp→ (j , d)) (λ hf → Node P w (snd (fst hf)))
    W→-nd-eqv w d = equiv (W→-nd-to w d) (W→-nd-from w d)
      (W→-nd-to-from w d) (W→-nd-from-to w d)

    --
    -- Using the above equivalences, we can define the induced action of a
    -- morphism on frames and families.
    --

    -- Reorganize?
    Frame→ : {i : I} (w : W P i) (f : Op P i)
      → Frame P w f → Frame Q (W→ w) (Op→ f)
    Frame→ w f α j = (Param≃ f {j})⁻¹ ∘e Σ-emap-r (α ∘ fst) ∘e (W→-lf-eqv w j)

    Relator← : Relator Q → Relator P
    Relator← R w f α = R (W→ w) (Op→ f) (Frame→ w f α)

    //-fmap : (F : Relator Q) → (P // Relator← F) →ₚ (Q // F)
    _→ₚ_.Sort→ (//-fmap F) = SortOp→ 
    _→ₚ_.Op→ (//-fmap F) (w , α , r) = W→ w , Frame→ w _ α , r
    _→ₚ_.Param≃ (//-fmap F) (w , α , r) {j , d} = W→-nd-eqv w d

  -- ... and hence so are domains
  {-# TERMINATING #-}
  Domain← : ∀ {ℓ} {I J : Type ℓ} {P : Poly I} {Q : Poly J} → P →ₚ Q → Domain Q → Domain P
  Rl (Domain← α D) = Relator← α (Rl D)
  Dm (Domain← α D) = Domain← (//-fmap α (Rl D)) (Dm D)

  Extension : ∀ {ℓ} {I : Type ℓ} {P : Poly I} (R : Relator P) → Type (lsucc ℓ)
  Extension {ℓ} {I} {P} R = {i : I} (w : W P i) (f : Op P i) (α : Frame P w f) (r : R w f α) → Type ℓ

  ΣRel : ∀ {ℓ} {I : Type ℓ} {P : Poly I} (R : Relator P) (E : Extension R) → Relator P
  ΣRel R E w f α = Σ (R w f α) (E w f α)

  ExtendedPoly : ∀ {ℓ} {I : Type ℓ} {P : Poly I} (R : Relator P) (E : Extension R) → Poly (Σ I (Op P))
  Op (ExtendedPoly {P = P} R E) (i , f) = Σ (Op (P // R) (i , f)) (λ { (w , α , r) → E w f α r })
  Param (ExtendedPoly {P = P} R E) (f , _) = Param (P // R) f

  ExtendedFst : ∀ {ℓ} {I : Type ℓ} {P : Poly I} (R : Relator P) (E : Extension R) → (P // ΣRel R E) →ₚ (P // R)
  _→ₚ_.Sort→ (ExtendedFst {I = I} {P} R E) = idf (Σ I (Op P))
  _→ₚ_.Op→ (ExtendedFst R E) (w , α , r , y) = (w , α , r)
  _→ₚ_.Param≃ (ExtendedFst {P = P} R E) (w , α , r , y) {j , d} = equiv to from to-from from-to

    where to : Node P w d → Σ (hfiber (λ x₁ → x₁) (j , d))(Param (P // R) (w , α , r) ∘ fst)
          to n = ((j , d) , idp) , n

          from : Σ (hfiber (λ x₁ → x₁) (j , d))(Param (P // ΣRel R E) (w , α , r , y) ∘ fst) → Node P w d
          from (((j , d) , idp) , n) = n

          to-from : (n : Σ (hfiber (λ x₁ → x₁) (j , d))(Param (P // ΣRel R E) (w , α , r , y) ∘ fst)) → to (from n) == n
          to-from (((j , d) , idp) , n) = idp

          from-to : (n : Node P w d) → from (to n) == n
          from-to n = idp

  ExtendedPrj : ∀ {ℓ} {I : Type ℓ} {P : Poly I} (R : Relator P) (E : Extension R) → ExtendedPoly R E →ₚ (P // R)
  _→ₚ_.Sort→ (ExtendedPrj {I = I} {P} R E) = idf (Σ I (Op P))
  _→ₚ_.Op→ (ExtendedPrj R E) = fst
  _→ₚ_.Param≃ (ExtendedPrj {P = P} R E) ((w , α , r) , y) {j , d} = equiv to from to-from from-to

    where to : Node P w d → Σ (hfiber (λ x₁ → x₁) (j , d))(Param (P // R) (w , α , r) ∘ fst)
          to n = ((j , d) , idp) , n

          from : Σ (hfiber (λ x₁ → x₁) (j , d))(Param (P // R) (w , α , r) ∘ fst) → Node P w d
          from (((j , d) , idp) , n) = n

          to-from : (n : Σ (hfiber (λ x₁ → x₁) (j , d))(Param (P // R) (w , α , r) ∘ fst)) → to (from n) == n
          to-from (((j , d) , idp) , n) = idp

          from-to : (n : Node P w d) → from (to n) == n
          from-to n = idp
          
  open _→ₚ_

  --
  --  Equivalences of polynomials
  --

  record is-poly-equiv {ℓ} {I J : Type ℓ} {P : Poly I} {Q : Poly J} (α : P →ₚ Q) : Type ℓ where
    constructor peq
    field
      Sort→-equiv : is-equiv (Sort→ α)
      Op→-equiv : {i : I} → is-equiv (Op→ α {i})

  _≃ₚ_ : ∀ {ℓ} {I J : Type ℓ} (P : Poly I) (Q : Poly J) → Type ℓ
  P ≃ₚ Q = Σ (P →ₚ Q) is-poly-equiv
  
  -- The equivalence between slicing an extension and directly giving the
  -- extended polynomial.
  ext-eqv-to : ∀ {ℓ} {I : Type ℓ} {P : Poly I} (R : Relator P) (E : Extension R)
    → (P // ΣRel R E) →ₚ ExtendedPoly R E
  Sort→ (ext-eqv-to {I = I} {P} R E) = idf (Σ I (Op P))
  Op→ (ext-eqv-to R E) (w , α , r , y) = (w , α , r) , y
  Param≃ (ext-eqv-to {P = P} R E) (w , α , r , y) {j} = equiv to from to-from from-to

    where to : Node P w (snd j) → Σ (hfiber (idf _) j) (Param (P // ΣRel R E) (w , α , r , y) ∘ fst)
          to n = (j , idp) , n

          from : Σ (hfiber (idf _) j) (Param (P // ΣRel R E) (w , α , r , y) ∘ fst) → Node P w (snd j)
          from ((j , idp) , n) = n

          to-from : (n : Σ (hfiber (idf _) j) (Param (P // ΣRel R E) (w , α , r , y) ∘ fst))
                    → to (from n) == n
          to-from ((j , idp) , n) = idp

          from-to : (n : Node P w (snd j)) → from (to n) == n
          from-to n = idp

  ext-eqv-is-equiv : ∀ {ℓ} {I : Type ℓ} {P : Poly I} (R : Relator P) (E : Extension R)
    → is-poly-equiv (ext-eqv-to R E)
  is-poly-equiv.Sort→-equiv (ext-eqv-is-equiv {I = I} {P} R E) = idf-is-equiv (Σ I (Op P))
  is-poly-equiv.Op→-equiv (ext-eqv-is-equiv R E) =
    is-eq (Op→ (ext-eqv-to R E)) (λ { ((w , α , r) , y) → w , α , r , y })
      (λ { ((w , α , r) , y) → idp }) (λ { (w , α , r , y) → idp })

  -- This version of the notion of equivalence seems somehow easier
  -- to work with, as opposed to the one below, but of course, should
  -- be equivalent
  -- 
  -- record PolyEqv {I J : Type ℓ} (P : Poly I) (Q : Poly J) : Type ℓ where
  --   field
  --     Sort≃ : I ≃ J
  --     Op≃ : (i : I) → Op P i ≃ Op Q (–> Sort≃ i)
  --     Param≃ : {i j : I} (f : Op P i) → Param P f j ≃ Param Q (–> (Op≃ i) c) (–> Sort≃ j)
