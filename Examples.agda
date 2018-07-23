{-# OPTIONS --without-K --rewriting --type-in-type #-}

open import HoTT
open import Util
open import Poly
open import PolyMonad

module Examples where

  𝕌 : Poly ⊤
  γ 𝕌 unit = Type₀
  ρ 𝕌 X unit = X

  PathFillers : {I : Type₀} (P : Poly I) (Fam : FillingFamily P)
    → FillingFamily (P // Fam)
  PathFillers P Fam {i , c} pd tgt f =
    flatten Fam pd == fst tgt

  -- PathFillers' : {I : Type₀} (P : Poly I) (Fam : FillingFamily P)
  --   → FillingFamily (P // Fam)
  -- PathFillers' P Fam {i , c} pd tgt f = flatten Fam pd , flatten-frm Fam pd , {!!} == tgt

  PathDomain : {I : Type₀} (P : Poly I) (Fam : FillingFamily P)
    → PolyDomain (P // Fam)
  F (PathDomain P Fam) = PathFillers P Fam 
  H (PathDomain P Fam) = PathDomain (P // Fam) (PathFillers P Fam)

  𝕌-Domain : PolyDomain 𝕌
  F 𝕌-Domain = λ w c f → ⊤
  H 𝕌-Domain = PathDomain 𝕌 (λ w c f → ⊤)

  -- What happens if we try to show the universe is a monad?
  𝕌-Mnd : is-algebraic 𝕌-Domain
  is-fillable 𝕌-Mnd w = has-level-in ((Leaf 𝕌 w unit , (λ { unit → ide (Leaf 𝕌 w unit) }) , tt) , λ { (X , e , unit) → {!!} })
  is-coherent 𝕌-Mnd X = inhab-conn (tt , idp)
  coh-algebraic 𝕌-Mnd = {!!}

  -- Yup, and there you have it.  Only thing left to understand is this
  -- coinductive process for the path fillers.  The claim you want to
  -- make is that, if you know a family is uniquely fillable, and that
  -- its path domain extension has a filling pair, then you can unfold
  -- once and this remains true.

  -- I believe a proof of this would give you both the universe and
  -- free monads.  But obviously there is still something to understand...
  
  pths-has-fillers : {I : Type₀} (P : Poly I) (F : FillingFamily P)
    → (is-f : {i : I} (w : W P i) → is-contr (CompositeFor P F w))
    → (is-h : {i : I} {c : γ P i} (tr : W (P // F) (i , c)) → is-connected -1 (bd-type P F (PathFillers P F) tr))
    → {ic : Σ I (γ P)} → (pd : W (P // F) ic) → is-contr (CompositeFor (P // F) (PathFillers P F) pd) 
  pths-has-fillers P F is-f is-h pd = Trunc-rec {n = S ⟨-2⟩} {A = bd-type P F (PathFillers P F) pd}
                                        {B = is-contr (CompositeFor (P // F) (PathFillers P F) pd)} lem mere-bd-filler

    where mere-bd-filler : Trunc (S ⟨-2⟩) (bd-type P F (PathFillers P F) pd)
          mere-bd-filler = fst (has-level-apply (is-h pd))

          ctr : bd-type P F (PathFillers P F) pd → CompositeFor (P // F) (PathFillers P F) pd
          ctr (f₀ , f₁) = (flatten F pd , flatten-frm F pd , f₀) , bd-frame F pd , f₁

          pth : (ff : bd-type P F (PathFillers P F) pd) (cmp : CompositeFor (P // F) (PathFillers P F) pd)
            → ctr ff == cmp
          pth (f₀ , f₁) ((._ , y , z) , a , idp) = pair= (pair= f₁ {!!}) {!!}

          lem : bd-type P F (PathFillers P F) pd → is-contr (CompositeFor (P // F) (PathFillers P F) pd)
          lem ff = has-level-in (ctr ff , pth ff)

  -- Umm.  It looks like I could strengthen the equality to be an equality among full frames, which
  -- would solve the first part.  But what about the second, where I have to show that every possible
  -- composite (is?) lives in the bd-frame.  Yeah, still something to understand here....
