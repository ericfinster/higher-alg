{-# OPTIONS --without-K --rewriting --type-in-type #-}

open import Base

module FramedSet where

  record BiGlobSet (I : Set) : Set where
    coinductive
    field
      Src : I → Set
      Tgt : I → Set
      Plc : (i : I) → Src i → Set
      Clr : (i : I) (s : Src i) (p : Plc i s) → I
      Ocp : (i : I) (s : Src i) (p : Plc i s) → Tgt (Clr i s p)
      Then : BiGlobSet (Σ I (λ i → Σ (Src i) (λ s → Tgt i)))

  open BiGlobSet

  Up : {I : Set} (B : BiGlobSet I) (X : I → Set) → BiGlobSet (Σ I X)
  Src (Up B X) (i , x) = Σ (Src B i) (λ s → (p : Plc B i s) → X (Clr B i s p))
  Tgt (Up B X) (i , x) = Tgt B i
  Plc (Up B X) (i , x) (s , ϕ) = Plc B i s
  Clr (Up B X) (i , x) (s , ϕ) p = (Clr B i s p , ϕ p)
  Ocp (Up B X) (i , x) (s , ϕ) p = Ocp B i s p
  Then (Up B X) =
    let X' = λ { (i , s , t) → Σ (X i) (λ _ → (p : Plc B i s) → X (Clr B i s p)) }
        res = Up (Then B) X'
    in {!res!}

  record BiOpTyp {I : Set} (B : BiGlobSet I) : Set where
    coinductive
    field
      X : (i : I) → Set
      TheRest : BiOpTyp (Then (Up B X))
