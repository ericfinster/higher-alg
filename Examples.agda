{-# OPTIONS --without-K --rewriting --type-in-type #-}

open import HoTT
open import Util
open import Polynomial
open import PolyMonad

module Examples where

  𝕌 : Poly ⊤
  γ 𝕌 unit = Type₀
  ρ 𝕌 X unit = X

  Sectioned : {I : Type₀} {P : Poly I} (F : FillingFamily P) → Type₀
  Sectioned {I} {P} F = {i : I} {c : γ P i} (pd : W (P // F) (i , c)) → F (flatten F pd) c (flatten-frm F pd)

  SectionedFillers : {I : Type₀} (P : Poly I) (F : FillingFamily P)
    → Sectioned F
    → FillingFamily (P // F)
  SectionedFillers P F σ {i , c} pd tgt ff =
    (tgt , ff) == ((flatten F pd , flatten-frm F pd , σ pd) , bd-frame F pd)

  -- Right, so this is pretty huge.  What does it get you?
  sectioned-lemma : {I : Type₀} (P : Poly I) (F : FillingFamily P)
    → (σ : Sectioned F)
    → {i : I} {c : γ P i} (pd : W (P // F) (i , c)) → is-contr (CompositeFor (SectionedFillers P F σ) pd)
  sectioned-lemma P F σ {i} {c} pd = has-level-in (ctr , pth)

    where ctr : CompositeFor (SectionedFillers P F σ) pd
          ctr = (flatten F pd , flatten-frm F pd , σ pd) , bd-frame F pd , idp

          pth : (x : CompositeFor (SectionedFillers P F σ) pd) → ctr == x
          pth ((._ , ._ , ._) , ._ , idp) = idp

  -- So like, I guess the lemma needs to be that if a family is sectioned, so is
  -- the family of sectioned fillers.  And for this, I guess you will have to
  -- argue by induction on the pasting diagram.  Could get messy, but I think
  -- somewhere a calculation like this must appear.

  conj : {I : Type₀} (P : Poly I) (F : FillingFamily P)
    → (σ : Sectioned F)
    → Sectioned (SectionedFillers P F σ)
  conj P F σ {i , c₀} {lf .i , f , x} (lf ._) = {!!}
  conj P F σ {i , c₀} {nd (c , δ) , f , x} (lf ._) = {!!}
  conj P F σ {i , c₀} {lf .i , f , x} (nd ((s , t , u) , ε)) = {!!}
  conj P F σ {i , c₀} {nd (c , δ) , f , x} (nd (α , ε)) = {!!}

  SectionedDomain : {I : Type₀} (P : Poly I) (F : FillingFamily P)
    → (σ : Sectioned F)
    → PolyDomain (P // F)
  F (SectionedDomain P F σ) = SectionedFillers P F σ
  H (SectionedDomain P F σ) = SectionedDomain (P // F) (SectionedFillers P F σ) (conj P F σ)

  SectionedMonad : {I : Type₀} (P : Poly I) (F : FillingFamily P)
    → (σ : Sectioned F)
    → is-algebraic (SectionedDomain P F σ)
  is-fillable (SectionedMonad P F σ) = sectioned-lemma P F σ 
  is-coherent (SectionedMonad P F σ) = {!!}
  coh-algebraic (SectionedMonad P F σ) = SectionedMonad (P // F) (SectionedFillers P F σ) (conj P F σ)
