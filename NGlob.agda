{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Substitution
open import SubstCoh
open import Globularity

-- Attempts at fixing n-globularity
module NGlob where

  is-regular : ∀ {ℓ} {I : Type ℓ} (P : Poly I)
    → (R₀ : PolyRel P) (R₁ : PolyRel (P // R₀))
    → Type ℓ
  is-regular {I = I} P R₀ R₁ = {i : I} {f : Op P i}
    → (w : W P i) (α : Frame P w f) (r : R₀ w f α)
    → (pd : W (P // R₀) (i , f)) (β : Frame (P // R₀) pd (w , α , r))
    → R₁ pd (w , α , r) β
    → Σ (R₀ (flatten R₀ pd) f (flatten-frm R₀ pd))
        (λ s → Path {A = OutFrame (P // R₀) pd}
                 ((flatten R₀ pd , flatten-frm R₀ pd , s) , bd-frame R₀ pd)
                 ((w , α , r) , β))

  postulate

    globular : ∀ {ℓ} {I : Type ℓ} (P : Poly I)
      → (R₀ : PolyRel P) (R₁ : PolyRel (P // R₀))
      → (is-reg : is-regular P R₀ R₁)
      → {i : I} {f : Op P i}
      → (w : W P i) (α : Frame P w f) (r : R₀ w f α)
      → (coh : W ((P // R₀) // R₁) ((i , f) , (w , α , r)))
      → Σ (R₀ (flatten R₀ (flatten R₁ coh)) f (flatten-frm R₀ (flatten R₁ coh))) (λ s → 
          Path {A = OutFrame (P // R₀) (flatten R₁ coh)} 
             ((flatten R₀ (flatten R₁ coh) , flatten-frm R₀ (flatten R₁ coh) , s) , bd-frame R₀ (flatten R₁ coh))
             ((w , α , r) , flatten-frm R₁ coh))

    -- So there you go.  But this completely abstract version
    -- seems highly suspicious ...
    globular-tgt : ∀ {ℓ} {I : Type ℓ} (P : Poly I) (R₀ : PolyRel P)
      → (R₁ : PolyRel (P // R₀)) (R₂ : PolyRel ((P // R₀) // R₁))
      → (R₁-reg : is-regular P R₀ R₁) (R₂-reg : is-regular (P // R₀) R₁ R₂)
      → {i : I} {f : Op P i}
      → (w : W P i) (α : Frame P w f) (r₀ : R₀ w f α)
      → (pd : W (P // R₀) (i , f)) (β : Frame (P // R₀) pd (w , α , r₀)) (r₁ : R₁ pd (w , α , r₀) β)
      → (trp : W (((P // R₀) // R₁) // R₂) (((i , f) , w , α , r₀) , pd , β , r₁))
      → globular P R₀ R₁ R₁-reg w α r₀ (flatten R₂ trp)
        == R₁-reg w α r₀ (flatten R₁ (flatten R₂ trp)) (flatten-frm R₁ (flatten R₂ trp))
           (fst (globular (P // R₀) R₁ R₂ R₂-reg pd β r₁ trp)) 

    -- So, it seems there is one remaining coherence which is to say that, applying
    -- globular twice and projecting gives the same guy.  It seems to me that this
    -- is saying something about *target* globularity.

    -- Right, and so there should also be the fact that projecting off the first
    -- guy gives back the original (although I think you may want to set this up
    -- better and you might be able to make that equality definitional...)

    -- Yeah.  So like, with this extra fact, you would be able to show a couple
    -- of the remaining holes below.

    -- So, does the above make sense?  Intuitively speaking, the element of R₀
    -- is just r itself with its type fixed.  So the relation is regular if,
    -- given an R₁ witness, I know that the tree must be the flatten and that r
    -- must be the right guy.  And the claim simply becomes that, if this is
    -- true for the elements, then it remains true for a pasting diagram.

    -- Okay, said this way, this sounds reasonable.

  module _ {ℓ} {I : Type ℓ} (P : Poly I) (R₀ : PolyRel P) where

    R₁ : PolyRel (P // R₀)
    R₁ {i , f} pd (w , α , r) β = Σ (R₀ (flatten R₀ pd) f (flatten-frm R₀ pd))
      (λ s → Path {A = OutFrame (P // R₀) pd} 
        ((flatten R₀ pd , flatten-frm R₀ pd , s) , bd-frame R₀ pd)
        ((w , α , r) , β))

    R₁-regular : is-regular P R₀ R₁
    R₁-regular w α r pd β = idf _
    
    R₂ : PolyRel ((P // R₀) // R₁)
    R₂ {(i , f) , (w , α , r)} coh (pd , β , s) γ =
      Path {A = OutFrame ((P // R₀) // R₁) coh}
        ((flatten R₁ coh , flatten-frm R₁ coh , globular P R₀ R₁ R₁-regular w α r coh) , bd-frame R₁ coh)
        ((pd , β , s) , γ)

    R₂-mult : is-multiplicative ((P // R₀) // R₁) R₂
    R₂-mult {(i , f) , (w , α , r)} coh = has-level-in (ctr , pth)

      where ctr : Composite ((P // R₀) // R₁) R₂ coh
            ctr = (flatten R₁ coh , flatten-frm R₁ coh , globular P R₀ R₁ R₁-regular w α r coh) , bd-frame R₁ coh , idp 

            pth : (cmp : Composite ((P // R₀) // R₁) R₂ coh) → ctr == cmp
            pth ((._ , ._ , ._) , ._ , idp) = idp

    R₂-regular : is-regular (P // R₀) R₁ R₂
    R₂-regular {i , f} {w , α , r} pd β s coh γ t =
      globular P R₀ R₁ R₁-regular w α r coh , t

    R₃ : PolyRel (((P // R₀) // R₁) // R₂)
    R₃ {((i , f) , (w , α , r)) , (pd , β , s)} trpl (coh , γ , t) δ = 
      Path {A = OutFrame (((P // R₀) // R₁) // R₂) trpl}
        ((flatten R₂ trpl , flatten-frm R₂ trpl , pair= (pair= idp (pair= idp {!!})) {!!} ∙
          (snd (globular (P // R₀) R₁ R₂ R₂-regular pd β s trpl))) , bd-frame R₂ trpl)
        ((coh , γ , t) , δ)

    -- R₃-regular : is-regular ((P // R₀) // R₁) R₂ R₃
    -- R₃-regular {((i , f) , (w , α , r))} {(pd , β , s)} coh γ t trpl δ u =
    --   (pair= (pair= idp (pair= idp {!!})) {!!} ∙
    --       (snd (globular (P // R₀) R₁ R₂ R₂-regular pd β s trpl))) , u

    -- R₄ : PolyRel ((((P // R₀) // R₁) // R₂) // R₃)
    -- R₄ = {!!}

    -- So I have an idea: what if you split the globularity statement into two
    -- pieces, one which says that you get this identification and a second which
    -- says, given an appropriate path-over, you get a baez-dolan identification
    -- as well.

    -- Because you see over and over again that somehow the natural division
    -- is grouping the tree and frame together and working about the filler
    -- and baez-dolan frame after.  Maybe this would give you more flexibility.

    -- Well, well, well.  So now that looks pretty interesting.
    -- Uh, yeah.  This is starting to look completely doable.

    -- It very much looks to me like, given this one extra fact about the targets
    -- of iterated applications of globular, that the resulting sequence after
    -- n = 3 stabilizes and becomes provable by induction.

    --
    --  Generalizing over n ...
    --

    -- RSort : (n : ℕ) → Type ℓ
    -- RPoly : (n : ℕ) → Poly (RSort n)
    -- RRel : (n : ℕ) → PolyRel (RPoly n)

    -- RSort O = I
    -- RSort (S n) = Ops (RPoly n)

    -- RPoly O = P 
    -- RPoly (S n) = RPoly n // RRel n

    -- postulate

    --   1-glob : (n : ℕ) {i : RSort n} {f : Op (RPoly n) i}
    --     → (pd : W (RPoly n // RRel n) (i , f))
    --     → (w : W (RPoly n) i) (α : Frame (RPoly n) w f) (r : (RRel n) w f α)
    --     → (β : Frame (RPoly (S n)) pd (w , α , r))
    --     → Σ (RRel n (flatten (RRel n) pd) f (flatten-frm (RRel n) pd))
    --         (λ r₀ → Path {A = OutFrame (RPoly (S n)) pd}
    --                      ((flatten (RRel n) pd , flatten-frm (RRel n) pd , r₀) , bd-frame (RRel n) pd)
    --                      ((w , α , r) , β))

    -- n-glob : (n : ℕ) {i : RSort n} {f : Op (RPoly n) i}
    --   → (w : W (RPoly n) i) (α : Frame (RPoly n) w f) (r : (RRel n) w f α)
    --   → (coh : W ((RPoly n // RRel n) // RRel (S n)) ((i , f) , (w , α , r)))
    --   → RRel (S n) (flatten (RRel (S n)) coh) (w , α , r) (flatten-frm (RRel (S n)) coh)

    -- RRel O = R₀
    -- RRel (S O) {i , f} pd (w , α , r) β =
    --   Σ (R₀ (flatten R₀ pd) f (flatten-frm R₀ pd))
    --     (λ s → Path {A = OutFrame (P // R₀) pd} 
    --              ((flatten R₀ pd , flatten-frm R₀ pd , s) , bd-frame R₀ pd)
    --              ((w , α , r) , β))
    -- RRel (S (S n)) {(i , f) , (w , α , r)} coh (pd , β , s) γ =
    --   Path {A = OutFrame (RPoly (S n) // RRel (S n)) coh}
    --     ((flatten (RRel (S n)) coh , flatten-frm (RRel (S n)) coh , n-glob n w α r coh) , bd-frame (RRel (S n)) coh)
    --     ((pd , β , s) , γ)


    -- n-glob = {!!}
    
    -- -- n-glob O w α r coh = glob₁ w α r coh
    -- -- n-glob (S O) {i , f} {._ , ._ , r} pd ._ (.r , idp) coh = {!!}
    -- -- n-glob (S (S n)) {i , f} {w , α , r} pd β s coh = {!!}

    -- -- n-glob O w α r coh = glob₁ w α r coh
    -- -- n-glob (S O) {i , f} {w , α , r} pd β s coh = {!!}
    -- -- n-glob (S (S n)) {i , f} {w , α , r} pd β s coh = {!ih!}

    -- --   where ih : RRel (S (S n)) (flatten (RRel (S (S n))) (flatten (RRel (S (S (S n)))) coh)) (w , α , r)
    -- --                         (flatten-frm (RRel (S (S n))) (flatten (RRel (S (S (S n)))) coh))
    -- --         ih = n-glob (S n) w α r (flatten (RRel (S (S (S n)))) coh)


    -- -- n-glob (S n) {i , f} {w , α , r} pd β s coh = {! !}

    -- --   where ih : RRel (S n) (flatten (RRel (S n)) (flatten (RRel (S (S n))) coh)) (w , α , r)
    -- --                         (flatten-frm (RRel (S n)) (flatten (RRel (S (S n))) coh))
    -- --         ih = n-glob n w α r (flatten (RRel (S (S n))) coh)


