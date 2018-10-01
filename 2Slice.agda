{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Substitution

module 2Slice where

  module _ {ℓ} {I : Type ℓ} (P : Poly I) where

    --
    --  This guy's on deck!!
    --

    BD : Poly (Ops (Subst P))
    Op BD ((i , f) , w , α) = hfiber (μ-subst P) (w , α)
    Param BD (pd , e) = Node (Subst P) pd
    
    2Slice : Poly (Ops (Subst P))
    2Slice = Subst (Subst P)

    encode : {pd : Ops (Subst P)} → Op BD pd → Op 2Slice pd
    encode (w , idp) = w , bd-frm P w

    encode-tr : {pd : Ops (Subst P)} → W BD pd → W 2Slice pd
    encode-tr (lf i) = lf i
    encode-tr (nd ((w , idp) , κ)) = nd ((w , bd-frm P w) , λ j n → encode-tr (κ j n))

    -- Shouldn't this pair be an operation in Subst (Subst P) ?
    flatn₁ : {pd : Ops (Subst P)} → W BD pd → W (Subst P) (fst pd)
    flatn-frm₁ : {pd : Ops (Subst P)} (coh : W BD pd)
      → Frame (Subst P) (flatn₁ coh) (snd pd)

    flatn₁ (lf ((i , f) , w , α)) = corolla (Subst P) (w , α)
    flatn₁ (nd ((pd , e) , θ)) = subst (Subst P) pd (λ g n → flatn₁ (θ g n) , flatn-frm₁ (θ g n))

    flatn-frm₁ (lf ((i , f) , w , α)) = corolla-lf-eqv (Subst P) (w , α)
    flatn-frm₁ (nd ((pd , idp) , θ)) j = bd-frm P pd j ∘e
      (subst-lf-eqv (Subst P) pd (λ g n → flatn₁ (θ g n) , flatn-frm₁ (θ g n)) j)

    -- Exactly.
    w-bd-to-op : {pd : Ops (Subst P)} → W BD pd → Op (Subst (Subst P)) pd
    w-bd-to-op coh = flatn₁ coh , flatn-frm₁ coh

    -- flattening is compatible with vertical grafting in the substitution
    -- polynomial ...
    flatn-graft : {i : I} {f : Op P i} (coh : W (Subst P) (i , f))
      → (ψ : (g : Ops P) → Leaf (Subst P) coh g → W (Subst P) g)
      → flatn P (graft (Subst P) coh ψ) ==
        -- I guess this pair goes by another name, no ???
        subst P (flatn P coh) (λ g n → flatn P (ψ g (<– (bd-frm P coh g) n)) , flatn-frm P (ψ g (<– (bd-frm P coh g) n)))
    flatn-graft (lf (i , f)) ψ = graft-unit P (flatn P (ψ (i , f) idp))
    flatn-graft (nd ((w , α) , κ)) ψ = {!!} -- Associativity of subst?

    flatn-subst : {i : I} {f : Op P i} (coh : W (Subst P) (i , f))
      → (θ : (pd : Ops (Subst P)) → Node (Subst P) coh pd → W BD pd)
      → flatn P (subst (Subst P) coh (λ g n → flatn₁ (θ g n) , flatn-frm₁ (θ g n))) == flatn P coh
    flatn-subst (lf .(_ , _)) θ = idp
    flatn-subst {i} {f} (nd ((w , α) , κ)) θ = 
      let coh' = flatn₁ (θ ((i , f) , w , α) (inl idp))
      in {!flatn-graft coh'!}
      
  --   -- Okay, and this path-over looks like just an extra coherence
  --   -- of flatten-flatten.
  --   flatten-subst : (RR : Relator (P // R)) (is-normal : normal RR)
  --     → {i : I} {f : Op P i} (pd : W (P // R) (i , f))
  --     → (κ : (j : Σ (Σ I (Op P)) (Op (P // R))) → Node (P // R) pd (snd j) → W ((P // R) // RR) j)
  --     → flatten R (substitute RR pd κ) == flatten R pd 
  --   flatten-subst RR is-n (lf .(_ , _)) κ = idp
  --   flatten-subst RR is-n (nd ((w , α , r) , ψ)) κ =
  --     flatten-graft (flatten RR (κ (_ , w , α , r) (inl idp))) ψ' ∙
  --     ap (uncurry (substitute R)) (pair= (flatten-flatten RR is-n w α r (κ (_ , w , α , r) (inl idp))) {!!}) 

  --     where w' : W (P // R) _
  --           w' = flatten RR (κ (_ , w , α , r) (inl idp))

  --           ψ' : (j : Σ I (Op P)) → Leaf (P // R) w' j → W (P // R) j
  --           ψ' j l = substitute RR (ψ j (flatten-frm-to RR (κ (_ , w , α , r) (inl idp)) j l))
  --                      (λ ic n → κ ic (inr (j , flatten-frm-to RR (κ (_ , w , α , r) (inl idp)) j l , n)))

    flatn-flatn : {i : I} {f : Op P i} (w : W P i) (α : Frame P w f)
      → (coh : W BD ((i , f) , w , α))
      → flatn P (flatn₁ coh) == w 
    flatn-flatn w α (lf ._) = {!!} -- An obvious coherence of the substitution monad ...
    flatn-flatn ._ ._ (nd ((pd , idp) , θ)) = flatn-subst pd θ

  --   -- Yeah, so like, if our relation RR doesn't imply at least that
  --   -- flatten R pd == w, then I don't see how to finish this.
  --   flatten-flatten : (RR : Relator (P // R)) (is-normal : normal RR)
  --     → {i : I} {f : Op P i}
  --     → (w : W P i) (α : Frame P w f) (r : R w f α)
  --     → (γ : W ((P // R) // RR) ((i , f) , (w , α , r)))
  --     → flatten R (flatten RR γ) == w
  --   flatten-flatten RR is-n w α r (lf ._) = substitute-unit w
  --   flatten-flatten RR is-n w α r (nd ((pd , β , rr) , κ)) =
  --     flatten-subst RR is-n pd κ ∙ is-n pd (w , α , r) β rr

    flatn-frm-flatn : {i : I} {f : Op P i} (w : W P i) (α : Frame P w f)
      → (coh : W BD ((i , f) , w , α))
      → flatn-frm P (flatn₁ coh) == α [ (λ w → Frame P w f) ↓ flatn-flatn w α coh ]
    flatn-frm-flatn w α (lf ._) = {!!}
    flatn-frm-flatn w α (nd ((pd , idp) , θ)) = {!!}

    μ-bd : {pd : Ops (Subst P)} → W BD pd → Op BD pd
    μ-bd {(i , f) , (w , α)} coh = flatn₁ coh ,
      pair= (flatn-flatn w α coh) (flatn-frm-flatn w α coh)


    
