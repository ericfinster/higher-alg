{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Substitution

-- Attempts at fixing n-globularity
module NGlob where

  module _ {ℓ} {I : Type ℓ} {P : Poly I} (R₀ : PolyRel P)
    (σ₀ : {i : I} {f : Op P i} (pd : W (P // R₀) (i , f))
      → R₀ (flatten R₀ pd) f (flatten-frm R₀ pd)) where

    -- Okay, suppose we have a section.

    Q : PolyRel (P // R₀)
    Q {i , f} pd (w , α , r) β = 
      Path {A = OutFrame (P // R₀) pd} 
        ((flatten R₀ pd , flatten-frm R₀ pd , σ₀ pd) , bd-frame R₀ pd)
        ((w , α , r) , β)

    postulate

      flatten-flatten : {i : I} {f : Op P i}
        → (w : W P i) (α : Frame P w f) (r : R₀ w f α)
        → (coh : W ((P // R₀) // Q) ((i , f) , (w , α , r)))
        → flatten R₀ (flatten Q coh) == w

      flatten-frm-flatten : {i : I} {f : Op P i}
        → (w : W P i) (α : Frame P w f) (r : R₀ w f α)
        → (coh : W ((P // R₀) // Q) ((i , f) , (w , α , r)))
        → flatten-frm R₀ (flatten Q coh) == α
            [ (λ w₁ → Frame P w₁ f) ↓ flatten-flatten w α r coh ]

      flatten-bd-flatten : {i : I} {f : Op P i}
        → (w : W P i) (α : Frame P w f) (r : R₀ w f α)
        → (coh : W ((P // R₀) // Q) ((i , f) , (w , α , r)))
        → (s : R₀ (flatten R₀ (flatten Q coh)) f (flatten-frm R₀ (flatten Q coh)))
        → (q : s == r [ (λ x → R₀ (fst x) f (snd x)) ↓  pair= (flatten-flatten w α r coh) (flatten-frm-flatten w α r coh) ])
        → bd-frame R₀ (flatten Q coh) == flatten-frm Q coh
            [ Frame (P // R₀) (flatten Q coh) ↓ pair= (flatten-flatten w α r coh) (↓-Σ-in (flatten-frm-flatten w α r coh) q) ]


  module _ {ℓ} {I : Type ℓ} {P : Poly I} (R₀ : PolyRel P)
    (σ₀ : {i : I} {f : Op P i} (pd : W (P // R₀) (i , f))
      → R₀ (flatten R₀ pd) f (flatten-frm R₀ pd)) where

    R₁ : PolyRel (P // R₀)
    R₁ = Q R₀ σ₀

    postulate

      σ₀-coh : {i : I} {f : Op P i}
        → (w : W P i) (α : Frame P w f) (r : R₀ w f α)
        → (coh : W ((P // R₀) // R₁) ((i , f) , (w , α , r)))
        → σ₀ (flatten R₁ coh) == r
            [ (λ x → R₀ (fst x) f (snd x)) ↓ pair= (flatten-flatten R₀ σ₀ w α r coh) (flatten-frm-flatten R₀ σ₀ w α r coh) ]
  
    -- As well as their dependent counterparts...

    -- ↓-=-in : ∀ {i j} {A : Type i} {B : A → Type j} {f g : Π A B}
    --   {x y : A} {p : x == y} {u : g x == f x} {v : g y == f y}
    --   → (u ◃ apd f p) == (apd g p ▹ v)
    --   → (u == v [ (λ x → g x == f x) ↓ p ])
    -- ↓-=-in {B = B} {p = idp} {u} {v} q = ! (◃idp {B = B} u) ∙ q ∙ idp▹ {B = B} v

    -- Q : PolyRel (P // R₀)
    -- Q {i , f} pd (w , α , r) β = 
    --   Path {A = OutFrame (P // R₀) pd} 
    --     ((flatten R₀ pd , flatten-frm R₀ pd , σ₀ pd) , bd-frame R₀ pd)
    --     ((w , α , r) , β)

    -- Goal: PathOver
    --       (λ x →
    --          R₁ (fst x)
    --          (flatten (λ {;i} → R₀) pd , (λ j → flatten-frm R₀ pd j) , σ₀ pd)
    --          (snd x))
    --       (pair=
    --        (flatten-flatten (λ {;i} → R₁) (λ {;i} {;f} → σ₁) pd
    --         (bd-frame (λ {;i} → R₀) pd) idp trp)
    --        (flatten-frm-flatten (λ {;i} → R₁) (λ {;i} {;f} → σ₁) pd
    --         (bd-frame (λ {;i} → R₀) pd) idp trp))
    --       (σ₁ (flatten (λ {;i} → R₂) trp)) idp


    -- Okay.  So, ummm. Can you make a formal statement about the invariance property
    -- of flattening with respect to the choice of σ₀-coh?

    -- It should apply when I have a pasting diagram (pd : W (P // R₀) (i , f)).
    -- I want it to be the case that the relations in this pasting diagram are
    -- all obtained somehow from the equality over given above.  But I am not
    -- sure to completely understand what this means.

    -- But the claim, somehow, is that given a pasting diagram as above populated
    -- by such path overs, apping the flatten function to the resulting equality
    -- of trees gives the same path regardless of the choice of σ₀-coh.

    -- I think I am starting to see a way forward.  What seems incredibly bothersome is that
    -- I appear to be picking a coherence here out of a hat.  And that should never be good.
    -- And there is clearly no reason why the choice here should be unique in any way.

    -- *But*, what I seem to be claiming is that while not every other choice will be equal to this
    -- one, since the substitution functions ignore their relation argument, any other choice will
    -- induce the *same* equality after flattening, etc.

    -- Okay.  There must be something to this.  Or, at least, this clearly seems like
    -- a property that you have not yet learned to exploit.

    -- And my intuition for why the equality you are trying to prove below may actually
    -- be true is that it is a fancy version of the fact that ap'ing a constant function
    -- to *any* path results in the identity.

    -- So, from here the question is, can you repeat?  Let's write out
    -- what we need for the section:

    σ₁ : {f : Ops P} {w : Op (P // R₀) f}
      → (coh : W ((P // R₀) // R₁) (f , w))
      → R₁ (flatten R₁ coh) w (flatten-frm R₁ coh)
    σ₁ {i , f} {w , α , r} coh = pair= (pair= (flatten-flatten R₀ σ₀ w α r coh)
      (↓-Σ-in (flatten-frm-flatten R₀ σ₀ w α r coh) (σ₀-coh w α r coh)))
        (flatten-bd-flatten R₀ σ₀ w α r coh (σ₀ (flatten R₁ coh)) (σ₀-coh w α r coh))

    -- There you have it, pretty straightforward.
    -- The next step is the hard part.  The task is to
    -- show the above coherence in the *next* slice.

    -- I claim that this corresponds, essentially, to the
    -- *target* globularity condition.  And if it happens that
    -- it can be proven without additional hypotheses on σ₀,
    -- then I claim this implies the monad structure of 𝕌.

    R₂ : PolyRel ((P // R₀) // R₁)
    R₂ = Q R₁ σ₁

    -- σ₂ : {w : Ops (P // R₀)} {pd : Op ((P // R₀) // R₁) w} (trp : W (((P // R₀) // R₁) // R₂) (w , pd))
    --   → R₂ (flatten R₂ trp) pd (flatten-frm R₂ trp)
    -- σ₂ {(i , f) , (.(flatten R₀ pd) , .(flatten-frm R₀ pd) , .(σ₀ pd))} {pd , .(bd-frame R₀ pd) , idp} trp =
    --   pair= (pair= (flatten-flatten R₁ σ₁ pd (bd-frame R₀ pd) idp trp)
    --     (↓-Σ-in (flatten-frm-flatten R₁ σ₁ pd (bd-frame R₀ pd) idp trp) (↓-=-in {!!})))
    --       (flatten-bd-flatten R₁ σ₁ pd (bd-frame R₀ pd) idp trp (σ₁ (flatten R₂ trp)) {!!})

    -- Okay, so I claim that we should be able to reduce, after path induction
    -- to the following cases:

    module _ {i : I} {i : I} {f : Op P i}
      (pd : W (P // R₀) (i , f))
      (trp : W (((P // R₀) // R₁) // R₂) (((i , f) , flatten R₀ pd , flatten-frm R₀ pd , σ₀ pd) , pd , bd-frame R₀ pd , idp)) where
  
      canon-pth : (flatten R₁ (flatten R₂ trp) , flatten-frm R₁ (flatten R₂ trp)) == (pd , bd-frame R₀ pd)
      canon-pth = pair= (flatten-flatten R₁ σ₁ pd (bd-frame R₀ pd) idp trp)
        (flatten-frm-flatten R₁ σ₁ pd (bd-frame R₀ pd) idp trp)
        
      goal : σ₁ (flatten R₂ trp) == idp [ (λ x → R₁ (fst x) (flatten R₀ pd , flatten-frm R₀ pd , σ₀ pd) (snd x)) ↓ canon-pth ]
      goal = ↓-=-in {!!}

    -- Q : PolyRel (P // R₀)
    -- Q {i , f} pd (w , α , r) β = 
    --   Path {A = OutFrame (P // R₀) pd} 
    --     ((flatten R₀ pd , flatten-frm R₀ pd , σ₀ pd) , bd-frame R₀ pd)
    --     ((w , α , r) , β)

      -- flatten₂ : ap (flatten R₀) (flatten-flatten R₁ σ₁ pd (bd-frame R₀ pd) idp trp) ==
      --            flatten-flatten R₀ σ₀ (flatten R₀ pd) (flatten-frm R₀ pd) (σ₀ pd) (flatten R₂ trp)
      -- flatten₂ = {!!}

      -- apd↓ : ∀ {i j k} {A : Type i} {B : A → Type j} {C : (a : A) → B a → Type k}
      --   (f : {a : A} (b : B a) → C a b) {x y : A} {p : x == y}
      --   {u : B x} {v : B y} (q : u == v [ B ↓ p ])
      --   → f u == f v [ (λ xy → C (fst xy) (snd xy)) ↓ pair= p q ]
      -- apd↓ f {p = idp} idp = idp

      -- flatten-frm₂ : apd (flatten-frm R₀) (flatten-flatten R₁ σ₁ pd (bd-frame R₀ pd) idp trp) ==
      --                {!flatten-frm-flatten R₀ σ₀ (flatten R₀ pd) (flatten-frm R₀ pd) (σ₀ pd) (flatten R₂ trp)!}
      -- flatten-frm₂ = {!!}




