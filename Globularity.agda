{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Substitution
open import SubstCoh

module Globularity where

  module _ {ℓ} {I : Type ℓ} {P : Poly I} (R : PolyRel P)
    (X : Refinement R) (Y : Refinement (FlattenRel (ΣR R X))) where

    private
      R₀ = ΣR R X
      R₁ = ΣR (FlattenRel R₀) Y
      
    postulate

      flatten-flatten : {i : I} {f : Op P i}
        → (w : W P i) (α : Frame P w f) (r : R₀ w f α)
        → (coh : W ((P // R₀) // R₁) ((i , f) , (w , α , r)))
        → flatten R₀ (flatten R₁ coh) == w

      flatten-frm-flatten : {i : I} {f : Op P i}
        → (w : W P i) (α : Frame P w f) (r : R₀ w f α)
        → (coh : W ((P // R₀) // R₁) ((i , f) , (w , α , r)))
        → flatten-frm R₀ (flatten R₁ coh) == α
            [ (λ w₁ → Frame P w₁ f) ↓ flatten-flatten w α r coh ]

      flatten-bd-flatten : {i : I} {f : Op P i}
        → (w : W P i) (α : Frame P w f) (r : R₀ w f α)
        → (coh : W ((P // R₀) // R₁) ((i , f) , (w , α , r)))
        → (s : R₀ (flatten R₀ (flatten R₁ coh)) f (flatten-frm R₀ (flatten R₁ coh)))
        → (q : s == r [ (λ x → R₀ (fst x) f (snd x)) ↓  pair= (flatten-flatten w α r coh) (flatten-frm-flatten w α r coh) ])
        → bd-frame R₀ (flatten R₁ coh) == flatten-frm R₁ coh
            [ Frame (P // R₀) (flatten R₁ coh) ↓ pair= (flatten-flatten w α r coh) (↓-Σ-in (flatten-frm-flatten w α r coh) q) ]


    globularity : {i : I} {f : Op P i}
      → (w : W P i) (α : Frame P w f) (r : R₀ w f α)
      → (coh : W ((P // R₀) // R₁) ((i , f) , (w , α , r)))
      → (s : R₀ (flatten R₀ (flatten R₁ coh)) f (flatten-frm R₀ (flatten R₁ coh)))
      → (q : s == r [ (λ x → R₀ (fst x) f (snd x)) ↓  pair= (flatten-flatten w α r coh) (flatten-frm-flatten w α r coh) ])
      → Path {A = Σ (Op (P // R₀) (i , f)) (Frame (P // R₀) (flatten R₁ coh))}
             ((flatten R₀ (flatten R₁ coh) , flatten-frm R₀ (flatten R₁ coh) , s) , bd-frame R₀ (flatten R₁ coh))
             ((w , α , r) , flatten-frm R₁ coh)
    globularity w α r coh s q = pair= (pair= (flatten-flatten w α r coh)
      (↓-Σ-in (flatten-frm-flatten w α r coh) q)) (flatten-bd-flatten w α r coh s q)

    -- This kind of thing should reall by cleaned up.
    -- Also, you could use sectioning a bit better here ..
    glob-transp : {i : I} {f : Op P i}
      → (w : W P i) (α : Frame P w f) (r : R₀ w f α)
      → (coh : W ((P // R₀) // R₁) ((i , f) , (w , α , r)))
      → R₀ (flatten R₀ (flatten R₁ coh)) f (flatten-frm R₀ (flatten R₁ coh))
    glob-transp {f = f} w α r coh = transport! (λ x → R₀ (fst x) f (snd x))
      (pair= (flatten-flatten w α r coh) (flatten-frm-flatten w α r coh)) r

    transp-globularity : {i : I} {f : Op P i}
      → (w : W P i) (α : Frame P w f) (r : R₀ w f α)
      → (coh : W ((P // R₀) // R₁) ((i , f) , (w , α , r)))
      → Path {A = Σ (Op (P // R₀) (i , f)) (Frame (P // R₀) (flatten R₁ coh))}
             ((flatten R₀ (flatten R₁ coh) , flatten-frm R₀ (flatten R₁ coh) , glob-transp w α r coh) , bd-frame R₀ (flatten R₁ coh))
             ((w , α , r) , flatten-frm R₁ coh)
    transp-globularity {f = f} w α r coh = globularity w α r coh (glob-transp w α r coh)
      (from-transp! (λ x → R₀ (fst x) f (snd x)) (pair= (flatten-flatten w α r coh) (flatten-frm-flatten w α r coh)) idp)
      
    -- Umm, yeah, so like, there's some kind of extra fact about the baez-dolan
    -- frame being flatten in the next dimension ... what to make of it?

