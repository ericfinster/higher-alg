{-# OPTIONS --without-K --rewriting --type-in-type #-}

open import HoTT
open import Util
open import Polynomial
open import Substitution
open import SubstCoh
open import PolyMonad

module Examples where

  𝕌 : Poly ⊤
  γ 𝕌 unit = Type₀
  ρ 𝕌 X unit = X

  𝕌-Family : FillingFamily 𝕌
  𝕌-Family w X f = ⊤

  module _ {I : Type₀} {P : Poly I} (F : FillingFamily P)
    {i : I} {c : γ P i} (pd : W (P // F) (i , c)) 
    (w : W P i) (f : Frame P w c) (x : F w c f) (ff : Frame (P // F) pd (w , f , x)) where

    tx : (wp : w == flatten F pd)
      → (fp : f == flatten-frm F pd [ (λ w₀ → Frame P w₀ c) ↓ wp ])
      → F (flatten F pd) c (flatten-frm F pd)
    tx idp idp = x 

    finally : (wp : w == flatten F pd)
      → (fp : f == flatten-frm F pd [ (λ w₀ → Frame P w₀ c) ↓ wp ])
      → Path {A = Σ (W P i) (λ w₀ → Σ (Frame P w₀ c) (λ f₀ → F w₀ c f₀))}
             (w , f , x) (flatten F pd , flatten-frm F pd , tx wp fp)
    finally idp idp = idp

    record CanonicalFiller  : Type₀ where
      constructor cf
      field

        w-pth : w == flatten F pd
        f-pth : f == flatten-frm F pd [ (λ w₀ → Frame P w₀ c) ↓ w-pth ]
        ff-pth : ff == bd-frame F pd [ (λ { (w₀ , f₀ , x₀) → Frame (P // F) pd (w₀ , f₀ , x₀) }) ↓ finally w-pth f-pth ] 

  CanonicalFamily : {I : Type₀} {P : Poly I} (F : FillingFamily P)
   → FillingFamily (P // F)
  CanonicalFamily F {i , c} pd (w , f , x) = CanonicalFiller F pd w f x

  module _ {I : Type₀} {P : Poly I} (F : FillingFamily P)
    (is-c : {i : I} {c : γ P i} (pd : W (P // F) (i , c)) → is-contr (CoherenceFor (CanonicalFamily F) pd)) where

    -- Okay, this seems like progress because we no longer have a completely arbitrary
    -- section running around that we have to be compatible with.  It seems that the
    -- equations are completely general coherences related to the Baez-Dolan construction.
    conj : {ic : Σ I (γ P)} {cc : γ (P // F) ic} (coh : W ((P // F) // CanonicalFamily F) (ic , cc))
      → is-contr (CoherenceFor (CanonicalFamily (CanonicalFamily F)) coh)
    conj {i , c} {w , f , x} (lf .((i , c) , w , f , x)) = has-level-in ({!!} , {!!})

      where ctr : CoherenceFor (CanonicalFamily (CanonicalFamily F)) (lf ((i , c) , w , f , x))
            ctr = (cf (substitute-unit F w) {!!} {!!}) , (cf idp idp idp)

            pth : (coh : CoherenceFor (CanonicalFamily (CanonicalFamily F)) (lf ((i , c) , w , f , x)))
              → ctr == coh
            pth (f₀ , cf w-pth f-pth ff-pth) = {!!}
                    
      -- has-level-in (((cf (substitute-unit F w) {!!} {!!}) , (cf idp idp idp)) , {!!})
    conj {i , c} {.(flatten F pd) , .(flatten-frm F pd) , x} (nd ((pd , .(bd-frame F pd) , cf idp idp idp) , sf)) =
      has-level-in (((cf {!!} {!!} {!!}) , (cf idp idp idp)) , {!!})


  -- Right, interesting.  So then, doesn't it seem like this map ought to be
  -- an equivalence?  And then, if that's the case, wouldn't a proof that this
  -- was contractible finish the job?
  CanonicalInverse : {I : Type₀} {P : Poly I} (F : FillingFamily P)
    → {i : I} {c : γ P i} (pd : W (P // F) (i , c))
    → CompositeFor (CanonicalFamily F) pd → CoherenceFor (CanonicalFamily F) pd
  CanonicalInverse F pd ((.(flatten F pd) , .(flatten-frm F pd) , x) , .(bd-frame F pd) , cf idp idp idp) =
    x , cf idp idp idp

  CanonicalToFrom : {I : Type₀} {P : Poly I} (F : FillingFamily P)
    → {i : I} {c : γ P i} (pd : W (P // F) (i , c))
    → (cmp : CompositeFor (CanonicalFamily F) pd)
    → CoherenceToComposite (CanonicalFamily F) pd (CanonicalInverse F pd cmp) == cmp
  CanonicalToFrom F pd ((.(flatten F pd) , .(flatten-frm F pd) , x) , .(bd-frame F pd) , cf idp idp idp) = idp

  -- So here we get stuck.  However, if we assume the coherences were contractible,
  -- then we would finish.  And that would imply the uniqueness of composites in the
  -- next dimension.  And we would be left to prove that this property was inherited
  -- by the next canonical family ...
  CanonicalFromTo : {I : Type₀} {P : Poly I} (F : FillingFamily P)
    → {i : I} {c : γ P i} (pd : W (P // F) (i , c))
    → (coh : CoherenceFor (CanonicalFamily F) pd)
    → CanonicalInverse F pd (CoherenceToComposite (CanonicalFamily F) pd coh) == coh
  CanonicalFromTo F pd (x , cf w-pth f-pth ff-pth) = {!!}


  -- CoherenceFor : {I : Type₀} {P : Poly I} {F : FillingFamily P} (FF : FillingFamily (P // F))
  --   {i : I} {c : γ P i} (pd : W (P // F) (i , c)) → Type₀
  -- CoherenceFor {P = P} {F} FF {c = c} pd = Σ (F (flatten F pd) c (flatten-frm F pd))
  --   (λ f → FF pd (flatten F pd , flatten-frm F pd , f) (bd-frame F pd))

  -- CanonicalHasFillers : {I : Type₀} {P : Poly I} (F : FillingFamily P)
  --   → (is-f : {i : I} (w : W P i) → is-contr (CompositeFor F w))
  --   → (is-c : {i : I} {c : γ P i} (pd : W (P // F) (i , c)) → is-contr (CoherenceFor (CanonicalFamily F) pd))
  --   → {ic : Σ I (γ P)} (pd : W (P // F) ic) → is-contr (CompositeFor (CanonicalFamily F) pd)
  -- CanonicalHasFillers F is-f is-c pd = has-level-in ({!!} , {!!})

  --   where ctr : CompositeFor (CanonicalFamily F) pd
  --         ctr = (flatten F pd , flatten-frm F pd , {!!}) , bd-frame F pd , cf idp idp idp

  --         pth : (x : CompositeFor (CanonicalFamily F) pd) → ctr == x
  --         pth ((._ , ._ , x) , ._ , (cf idp idp idp)) = {!!}

  -- -- frame-and-target : {I : Type₀} {P : Poly I} (F : FillingFamily P)
  -- --   → (is-f : {i : I} (w : W P i) → is-contr (CompositeFor F w))
  -- --   → {i : I} (w : W P i) → Σ (γ P i) (Frame P w)
  -- -- frame-and-target F is-f w = let cmp = contr-center (is-f w) in fst cmp , fst (snd cmp)

  -- -- module _ {I : Type₀} {P : Poly I} (F : FillingFamily P)
  -- --   (is-f : {i : I} (w : W P i) → is-contr (CompositeFor F w))
  -- --   (hyp : {i : I} {c : γ P i} (pd : W (P // F) (i , c))
  -- --       → frame-and-target F is-f (flatten F pd) == c , flatten-frm F pd) where

  -- --   filler : {i : I} {c : γ P i} (pd : W (P // F) (i , c)) → F (flatten F pd) c (flatten-frm F pd)
  -- --   filler pd = transport (λ pr → F (flatten F pd) (fst pr) (snd pr)) (hyp pd) (snd (snd (contr-center (is-f (flatten F pd)))))

  -- --   path-family : FillingFamily (P // F)
  -- --   path-family {i , c} pd (w , f , x) ff =
  -- --     Path {A = Σ (Σ (W P i) (λ w₀ → Σ (Frame P w₀ c) (F w₀ c))) (Frame (P // F) pd) }
  -- --       ((w , f , x) , ff)
  -- --       ((flatten F pd , flatten-frm F pd , filler pd) , bd-frame F pd)

  -- --   path-is-f : {ic : Σ I (γ P)} (pd : W (P // F) ic) → is-contr (CompositeFor path-family pd)
  -- --   path-is-f {i , c} pd = has-level-in (ctr , pth) 
  
  -- --     where ctr : CompositeFor path-family pd
  -- --           ctr = ((flatten F pd , flatten-frm F pd , filler pd) , bd-frame F pd , idp)

  -- --           pth : (coh : CompositeFor path-family pd) → ctr == coh
  -- --           pth (.(flatten F pd , flatten-frm F pd , filler pd) , .(bd-frame F pd) , idp) = idp

  -- --   conj : {ic : Σ I (γ P)} {flr : γ (P // F) ic} (coh : W ((P // F) // path-family) (ic , flr))
  -- --     → frame-and-target path-family path-is-f (flatten path-family coh)
  -- --       == flr , flatten-frm path-family coh
  -- --   conj {i , c} {w , f , x} (lf .((i , c) , w , f , x)) = pair= (pair= {!!} {!!}) {!!}
  -- --   conj {i , c} {.(flatten F pd) , .(flatten-frm F pd) , .(filler pd)} (nd ((pd , .(bd-frame F pd) , idp) , sfrm)) = {!!}

  --   -- So, it seems we still end up with a proof to do by induction.
  --   -- Mmmm.  So maybe your previous formulation is in fact simpler,
  --   -- as it does not require this extra equality ...

  --   -- Indeed, in the current formulation, it appears that we are asked to prove a
  --   -- number of (pretty reasonable) equalities, that is, coherences about the baez-dolan
  --   -- construction.  I think these two forumations are basically equivalent: in the other
  --   -- formulation, we will be asked to create an element of the path filling family, which
  --   -- should be just the same as the equality we are being asked to produce here.

  --   -- Still, for some reason I seem to have a preference for the other formulation, as it involves
  --   -- one less equality....
    

  -- Sectioned : {I : Type₀} {P : Poly I} (F : FillingFamily P) → Type₀
  -- Sectioned {I} {P} F = {i : I} {c : γ P i} (pd : W (P // F) (i , c)) → F (flatten F pd) c (flatten-frm F pd)

  -- -- Ah, okay, maybe the interesting case is when its a *proposition*.
  -- -- Because it seems that this is what will happen in the case of set-level objects ...
  -- StrongSectioned : {I : Type₀} {P : Poly I} (F : FillingFamily P) → Type₀
  -- StrongSectioned {I} {P} F = {i : I} {c : γ P i} (pd : W (P // F) (i , c)) → is-contr (F (flatten F pd) c (flatten-frm F pd))

  -- SectionedFillers : {I : Type₀} (P : Poly I) (F : FillingFamily P)
  --   → Sectioned F
  --   → FillingFamily (P // F)
  -- SectionedFillers P F σ {i , c} pd (w , f , x) ff =
  --   Path {A = Σ (Σ (W P i) (λ w₀ → Σ (Frame P w₀ c) (F w₀ c))) (Frame (P // F) pd) }
  --     ((w , f , x) , ff)
  --     ((flatten F pd , flatten-frm F pd , σ pd) , bd-frame F pd)

  -- -- Right, so this is pretty huge.  What does it get you?
  -- sectioned-lemma : {I : Type₀} (P : Poly I) (F : FillingFamily P)
  --   → (σ : Sectioned F)
  --   → {i : I} {c : γ P i} (pd : W (P // F) (i , c)) → is-contr (CompositeFor (SectionedFillers P F σ) pd)
  -- sectioned-lemma P F σ {i} {c} pd = has-level-in (ctr , pth)

  --   where ctr : CompositeFor (SectionedFillers P F σ) pd
  --         ctr = (flatten F pd , flatten-frm F pd , σ pd) , bd-frame F pd , idp

  --         pth : (x : CompositeFor (SectionedFillers P F σ) pd) → ctr == x
  --         pth ((._ , ._ , ._) , ._ , idp) = idp

  -- conj : {I : Type₀} (P : Poly I) (F : FillingFamily P) (σ : Sectioned F)
  --   → Sectioned (SectionedFillers P F σ)
  -- conj P F σ {i , c} {w , f , x} (lf .((i , c) , w , f , x)) = pair= (pair= w-unit {!!}) {!!}

  --   where w-unit : w == substitute F w (λ j p → lf j)
  --         w-unit = {!!}

  --         crl : W (P // F) (i , c)
  --         crl = nd ((w , f , x) , λ j p → lf j)

  --         fpth : f == flatten-frm F crl [ (λ w₀ → Frame P w₀ c) ↓ w-unit ]
  --         fpth = {!!}

  --         -- This one is a bit of a question mark.  I don't necessarily see
  --         -- that there should be such a path.  What links your arbitrary x to
  --         -- the chosen σ?
  --         spth : x == σ crl [ uncurry (λ w₀ f₀ → F w₀ c f₀) ↓ pair= w-unit fpth ]
  --         spth = {!!}
          
  --         next : (f , x) == (flatten-frm F crl , σ crl) [ (λ w₀ → Σ (Frame P w₀ c) (F w₀ c)) ↓ w-unit ]
  --         next = ↓-Σ-in {A = W P i} {B = λ w₀ → Frame P w₀ c} {C = λ w₀ f → F w₀ c f}
  --                       {p = w-unit} {r = f} {r' = flatten-frm F crl}
  --                       {s = x} {s' = σ crl}
  --                       fpth {!!} -- spth

  -- -- ↓-Σ-in : {x x' : A} {p : x == x'} {r : B x} {r' : B x'}
  -- --   {s : C x r} {s' : C x' r'}
  -- --   (q : r == r' [ B ↓ p ])
  -- --   → s == s' [ uncurry C ↓ pair= p q ]
  -- --   → (r , s) == (r' , s') [ (λ x → Σ (B x) (C x)) ↓ p ]
  -- -- ↓-Σ-in {p = idp} idp t = pair= idp t


  -- conj P F σ {i , c} {.(flatten F pd) , .(flatten-frm F pd) , .(σ pd)} (nd ((pd , .(bd-frame F pd) , idp) , κ)) = pair= (pair= {!!} {!!}) {!!}

  -- -- Indeed, after path induction, this theorem looks entirely reasonable, if tedious.
  -- -- Hmmm.  But on the other hand, if feels like we will need some more hypotheses on
  -- -- σ, since otherwise, why should this at all be connected with x?

  -- -- SectionedDomain : {I : Type₀} (P : Poly I) (F : FillingFamily P)
  -- --   → (σ : Sectioned F)
  -- --   → PolyDomain (P // F)
  -- -- F (SectionedDomain P F σ) = SectionedFillers P F σ
  -- -- H (SectionedDomain P F σ) = SectionedDomain (P // F) (SectionedFillers P F σ) (conj P F σ)

  -- -- SectionedMonad : {I : Type₀} (P : Poly I) (F : FillingFamily P)
  -- --   → (σ : Sectioned F)
  -- --   → is-algebraic (SectionedDomain P F σ)
  -- -- is-fillable (SectionedMonad P F σ) = sectioned-lemma P F σ 
  -- -- is-coherent (SectionedMonad P F σ) = {!!}
  -- -- coh-algebraic (SectionedMonad P F σ) = SectionedMonad (P // F) (SectionedFillers P F σ) (conj P F σ)
