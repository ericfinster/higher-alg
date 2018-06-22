{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import PolyMonads
open import PolyMonadUtil

module OpetopicTypes where

  record OpType {I : Type₀} (M : Mnd I) : Type₁ where
    coinductive
    field

      Ops : I → Type₀
      Rels : OpType (slc (pb M Ops))

  open OpType
  
  niche : {I : Type₀} {M : Mnd I} (X : OpType M) → I → Type₀
  niche {M = M} X i = ⟪ M ⟫ (Ops X) i

  filler : {I : Type₀} {M : Mnd I} (X : OpType M) {i : I} (n : niche X i) → Type₀
  filler X {i = i} n = Σ (Ops X i) (λ x → Ops (Rels X) ((i , x) , n))

  record is-algebraic {I : Type₀} {M : Mnd I} (X : OpType M) : Type₀ where
    coinductive
    field

      fillers-contr : {i : I} (n : niche X i) → is-contr (filler X n)
      rels-algebraic : is-algebraic (Rels X)

  open is-algebraic

  filler-of : {I : Type₀} {M : Mnd I} {X : OpType M} {i : I}
              (n : niche X i) (is-alg : is-algebraic X) → Ops X i
  filler-of n is-alg = fst (fst (has-level-apply (fillers-contr is-alg n)))              

  pth-to-id-cell : {I : Type₀} {M : Mnd I} (X : OpType M) (is-alg : is-algebraic X)
                   {i : I} (x y : Ops X i) (p : x == y) → 
                   Ops (Rels X) ((i , x) , (η M i , λ p → transport (Ops X) (ap (τ M) (ηρ-η M i p)) y))
  pth-to-id-cell {M = M} X is-coh {i} x .x idp = filler-of id-niche (rels-algebraic is-coh)

    where id-niche : niche (Rels X) (((i , x) , (η M i , λ p → transport (Ops X) (ap (τ M) (ηρ-η M i p)) x)))
          id-niche = dot (i , x) , λ { () }

  record is-complete {I : Type₀} {M : Mnd I} (X : OpType M) (is-alg : is-algebraic X) : Type₀ where
    coinductive
    field

      pth-to-id-equiv : {i : I} (x y : Ops X i) → is-equiv (pth-to-id-cell X is-alg x y)
      rels-is-complete : is-complete (Rels X) (rels-algebraic is-alg)

  open is-complete
  
  record ∞Alg {I : Type₀} (M : Mnd I) : Type₁ where
    field

      carrier : OpType M
      is-alg : is-algebraic carrier
      is-cmplt : is-complete carrier is-alg

  open ∞Alg
  
  Term : {I : Type₀} (M : Mnd I) → OpType M
  Ops (Term M) = cst ⊤
  Rels (Term M) = Term (slc (pb M (cst ⊤)))

  Term-is-algebraic : {I : Type₀} (M : Mnd I) → is-algebraic (Term M)
  fillers-contr (Term-is-algebraic M) n = has-level-in ((unit , unit) , λ { (unit , unit) → idp })
  rels-algebraic (Term-is-algebraic M) = Term-is-algebraic (slc (pb M (cst ⊤)))

  Term-is-complete : {I : Type₀} (M : Mnd I) → is-complete (Term M) (Term-is-algebraic M)
  pth-to-id-equiv (Term-is-complete {I} M) {i} unit unit =
    is-eq (pth-to-id-cell (Term M) (Term-is-algebraic M) {i = i} unit unit)
    (λ { unit → idp })
    (λ { unit → idp })
    (λ { idp → idp })
  rels-is-complete (Term-is-complete M) = Term-is-complete (slc (pb M (cst ⊤))) 

  TermAlg : {I : Type₀} (M : Mnd I) → ∞Alg M
  carrier (TermAlg M) = Term M
  is-alg (TermAlg M) = Term-is-algebraic M
  is-cmplt (TermAlg M) = Term-is-complete M

  FreeCarrier : {I : Type₀} (M : Mnd I) → (I → Type₀) → OpType M
  Ops (FreeCarrier M X) = ⟪ M ⟫ X
  Rels (FreeCarrier M X) = FreeCarrier (slc (pb M (⟪ M ⟫ X))) P

    where P : Σ (Σ _ (⟪ M ⟫ X)) (γ-pb M (⟪ M ⟫ X)) → Type₀
          P ((i , (c₀ , δ₀)) , (c , δ)) =
            let δ' = λ p₀ → fst (δ p₀) in
              (c₀ , δ₀) == (μ M c δ' , λ p → transport X (μρ-snd-coh M δ' p) (snd (δ (μρ-fst M δ' p)) (μρ-snd M δ' p)))
                          
  -- This looks better, right?  And now the idea is that you are
  -- going to put the identity type.  This will then be algebraic
  -- because of the contractibility of singleton types!

  -- Fucking brilliant.
  
  -- module _ {I : Type₀} (M : Mnd I) where

  --   -- I think this is true if X takes values in sets ...
  --   FreeAlgebraic : (X : I → Type₀) → is-algebraic (FreeCarrier X)
  --   fillers-contr (FreeAlgebraic X) (c , δ) = has-level-in (((μ M c (λ p → fst (δ p)) , λ p → {! !}) , ?) ,
  --     λ { ((c' , δ') , unit) → pair= {!!} {!!} })

  --     where δ' = snd (δ (μρ-fst M (λ p₀ → fst (δ p₀)) {!!}))
  --   rels-algebraic (FreeAlgebraic X) = ?

    -- No, there's something wrong here.  You're off by a dimension or
    -- something ... this can't be the right definition.  Indeed.  The
    -- filler should constrant the connection between the two...

    -- So, why should this be true?
    -- Yeah, I guess it probably isn't in general.
    -- Basically, you should need a bunch of guys to be sets.
    -- In that case, it's something like that, in order to be even well typed,
    -- we must have that the target is the multiplication of the source tree.
    -- Somehow nothing else can be sufficiently natural ....

    -- Yeah, uh, it should be that 

    -- Hmmm ....

    -- FreeAlg : (I → Type₀) → ∞Alg M
    -- FreeAlg X = {!!}

