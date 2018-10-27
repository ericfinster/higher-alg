{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Substitution
open import PolyMonad

module Pullback where

  module _ {ℓ} {I : Type ℓ} (P : Poly I) (X : I → Type ℓ) where

    -- Pulling back a polynomial along a family
    PbPoly : Poly (Σ I X)
    Op PbPoly (i , x) = ⟦ P ⟧ X i
    Param PbPoly (f , ϕ) (j , y) = Σ (Param P f j) (λ p → ϕ j p == y)

    -- erase all the intermediate decorations
    erase : {i : I} {x : X i} → W PbPoly (i , x) → W P i
    erase {i} {x} (lf ._) = lf i
    erase {i} {x} (nd ((f , ρ) , ϕ)) =
      let ϕ' j p = erase (ϕ (j , ρ j p) (p , idp))
      in nd (f , ϕ')

    -- find an erased leaf
    erase-lf : {i : I} {x : X i} (w : W PbPoly (i , x))
      → (j  : I) (y : X j)
      → Leaf PbPoly w (j , y) → Leaf P (erase w) j
    erase-lf (lf (i , x)) j y l = fst= l
    erase-lf (nd ((f , ρ) , ϕ)) j y ((k , ._) , (p , idp) , l) = 
      k , p , erase-lf (ϕ (k , ρ k p) (p , idp)) j y l
    
    -- retrieve the decoration at the leaves
    erase-dec : {i : I} {x : X i} (w : W PbPoly (i , x))
      → (j : I) (l : Leaf P (erase w) j) → X j
    erase-dec (lf (i , x)) j l = transport X l x
    erase-dec (nd ((f , ρ) , ϕ)) j (k , p , l) =
      erase-dec (ϕ (k , ρ k p) (p , idp)) j l

    -- the value at the erased leaf is the expected one
    erase-coh : {i : I} {x : X i} (w : W PbPoly (i , x))
      → (j  : I) (y : X j) (l : Leaf PbPoly w (j , y))
      → erase-dec w j (erase-lf w j y l) == y
    erase-coh (lf (i , x)) j y l = to-transp (snd= l)
    erase-coh (nd ((f , ρ) , ϕ)) j y ((k , ._) , (p , idp) , l) =
      erase-coh (ϕ (k , ρ k p) (p , idp)) j y l

    module _ (M : PolyMagma P) where
    
      -- Multipliction in the pullback simply "erases" the
      -- intermediate decorations
      μ-pb : {i : I} {x : X i} → W PbPoly (i , x) → ⟦ P ⟧ X i
      μ-pb w = μ M (erase w) , λ j p → erase-dec w j (<– (μ-frm M (erase w) j) p)

      μ-pb-frm-to : {i : I} {x : X i} (w : W PbPoly (i , x))
        → (j : I) (y : X j)
        → Leaf PbPoly w (j , y)
        → Σ (Param P (fst (μ-pb w)) j) (λ p → snd (μ-pb w) j p == y)
      μ-pb-frm-to (lf (i , x)) .i .x idp = –> (μ-frm M (lf i) i) idp ,
        ap (erase-dec (lf (i , x)) i) (<–-inv-l (μ-frm M (lf i) i) idp)
      μ-pb-frm-to {x = x} (nd ((f , ρ) , ϕ)) j y ((k , .(ρ k p)) , (p , idp) , l) =
        –> (μ-frm M (nd (f , ϕ')) j) (k , p , l') , lem
    
             where ϕ' : (j : I) → Param P f j → W P j
                   ϕ' j p = erase (ϕ (j , ρ j p) (p , idp))

                   l' : Leaf P (ϕ' k p) j
                   l' = erase-lf (ϕ (k , ρ k p) (p , idp)) j y l
                   
                   lem = erase-dec {x = x} (nd ((f , ρ) , ϕ)) j (<– (μ-frm M (nd (f , ϕ')) j) (–> (μ-frm M (nd (f , ϕ')) j) (k , p , l')))
                           =⟨ <–-inv-l (μ-frm M (nd (f , ϕ')) j) (k , p , l') |in-ctx (erase-dec {x = x} (nd ((f , ρ) , ϕ)) j) ⟩
                         erase-dec (ϕ (k , ρ k p) (p , idp)) j l'
                           =⟨ erase-coh (ϕ (k , ρ k p) (p , idp)) j y l ⟩ 
                         y ∎

      μ-pb-frm-from : {i : I} {x : X i} (w : W PbPoly (i , x))
        → (j : I) (y : X j)
        → Σ (Param P (fst (μ-pb w)) j) (λ p → snd (μ-pb w) j p == y)
        → Leaf PbPoly w (j , y)
      μ-pb-frm-from (lf (i , x)) j ._ (p , idp) =
        let pth = <– (μ-frm M (lf i) j) p
        in pair= pth (to-transp-↓ X pth x)
      μ-pb-frm-from (nd ((f , ρ) , ϕ)) j ._ (p , idp) = 
        let ϕ' j p = erase (ϕ (j , ρ j p) (p , idp))
            (k , q , l) = <– (μ-frm M (nd (f , ϕ')) j) p
        in (k , ρ k q) , (q , idp) , μ-pb-frm-from (ϕ (k , ρ k q) (q , idp)) j _ {!!}

      postulate

        μ-pb-frm-to-from : {i : I} {x : X i} (w : W PbPoly (i , x))
          → (j : I) (y : X j)
          → (q : Σ (Param P (fst (μ-pb w)) j) (λ p → snd (μ-pb w) j p == y))
          → μ-pb-frm-to w j y (μ-pb-frm-from w j y q) == q

        μ-pb-frm-from-to : {i : I} {x : X i} (w : W PbPoly (i , x))
          → (j : I) (y : X j)
          → (l : Leaf PbPoly w (j , y))
          → μ-pb-frm-from w j y (μ-pb-frm-to w j y l) == l

      μ-pb-frm : {i : I} {x : X i} (w : W PbPoly (i , x))
        → Frame PbPoly w (μ-pb w)
      μ-pb-frm w (j , y) =
        equiv (μ-pb-frm-to w j y) (μ-pb-frm-from w j y)
              (μ-pb-frm-to-from w j y) (μ-pb-frm-from-to w j y)

      PbMgm : PolyMagma PbPoly
      μ PbMgm = μ-pb  
      μ-frm PbMgm = μ-pb-frm

