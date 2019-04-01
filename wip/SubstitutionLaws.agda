{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Grafting
open import Biased

module wip.SubstitutionLaws {ℓ} {I : Type ℓ} (P : Poly I) (R : PolyRel P) where

  open import Substitution P
  open BiasedMgm
  open BiasedLaws

  subst-η : (f : Ops P) → InFrame P f
  subst-η (_ , f) = corolla P f , corolla-frm P f

  subst-η-dec : {i : I} (w : W P i) →
    (g : Ops P) (n : Node P w g) → InFrame P g
  subst-η-dec w g n = subst-η g

  subst-γ : (f : Ops P) (wα : InFrame P f)
    → (κ : (g : Ops P) → Node P (fst wα) g → InFrame P g) 
    → InFrame P f
  subst-γ (i , f) (w , α) κ =
    subst w κ , λ j → α j ∘e (subst-leaf-eqv w κ j) ⁻¹

  subst-η-frm : (f g : Ops P)
    → (f == g) ≃ (f == g) ⊔ Σ I (λ k → Σ (Param P (snd f) k) (λ p → Lift {j = ℓ} ⊥))
  subst-η-frm f g = equiv inl from to-from (λ _ → idp)

    where from : (f == g) ⊔ Σ I (λ k → Σ (Param P (snd f) k) (λ p → Lift ⊥)) → f == g
          from (inl e) = e
          from (inr (_ , _ , ()))

          to-from : (e : (f == g) ⊔ Σ I (λ k → Σ (Param P (snd f) k) (λ p → Lift ⊥)))
            → inl (from e) == e
          to-from (inl e) = idp
          to-from (inr (_ , _ , ()))


  -- The extra information required from a relation in order that we
  -- can construct a biased multiplication on the slice by R.
  record SubstRel : Type ℓ where
    field

      η-rel : (f : Ops P) → R f (subst-η f)
        
      γ-rel : (f : Ops P) (wα : InFrame P f) (r : R f wα)
        → (κ : (g : Ops P) → Node P (fst wα) g → Op (P // R) g) 
        → R f (subst-γ f wα (λ g n → fst (κ g n)))

  open SubstRel
  
  SubstBiasedMgm : SubstRel → BiasedMgm (P // R)
  η (SubstBiasedMgm SRel) f =
    subst-η f , η-rel SRel f
  η-frm (SubstBiasedMgm SRel) =
    subst-η-frm
  γ (SubstBiasedMgm SRel) {f} (wα , r) κ =
    let κ' g n = fst (κ g n)
    in subst-γ f wα κ' , γ-rel SRel f wα r κ
  γ-frm (SubstBiasedMgm SRel) ((w , α) , r) κ g =
    let κ' g n = fst (κ g n)
    in subst-node-eqv w κ' g

  -- --
  -- --  Unit left law
  -- --

  -- subst-unit-l : {i : I} (w : W P i)
  --   →  subst w (subst-η-dec w) == w
  -- subst-unit-l (lf i) = idp
  -- subst-unit-l (nd (f , ϕ)) = ap (λ x → nd (f , x))
  --   (Decor-== P (λ j p → subst-unit-l (ϕ j p)))

  -- subst-unit-l-lem : {i : I} (w : W P i)
  --   → (j : I) (l : Leaf P (subst w (subst-η-dec w)) j)
  --   → l == subst-leaf-from w (subst-η-dec w) j l [ (λ x → Leaf P x j) ↓ subst-unit-l w ]
  -- subst-unit-l-lem (lf i) j l = idp
  -- subst-unit-l-lem (nd (f , ϕ)) j (k , p , l) =
  --   ↓-ap-in (λ x → Leaf P x j)
  --           (λ x → nd (f , x))
  --           (↓-nd-Leaf-ih P (λ j₁ p₁ → subst-unit-l (ϕ j₁ p₁)) k p
  --                           (subst-unit-l-lem (ϕ k p) j l))

  -- subst-unit-l-frm : {i : I} {f : Op P i}
  --   → (w : W P i) (α : Frame P w f)
  --   → (λ j → α j ∘e (subst-leaf-eqv w (λ g n → subst-η g) j) ⁻¹)
  --       == α [ (λ x → Frame P x f) ↓ subst-unit-l w ]
  -- subst-unit-l-frm w α =
  --   let lem j l₀ l₁ q = –> (α j) (subst-leaf-from w (subst-η-dec w) j l₀)
  --                         =⟨ ! (to-transp (subst-unit-l-lem w j l₀)) |in-ctx (–> (α j)) ⟩
  --                       –> (α j) (transport (λ x → Leaf P x j) (subst-unit-l w) l₀)
  --                         =⟨ to-transp q |in-ctx (–> (α j)) ⟩ 
  --                       –> (α j) l₁ ∎
  --   in ↓-W-Frame-in P lem

  -- subst-node-unit-l : {i : I} (w : W P i)
  --   → (g : Ops P) (n : Node P w g)
  --   → subst-node-to w (subst-η-dec w) g (g , n , inl idp)
  --     == n [ (λ x → Node P x g) ↓ subst-unit-l w ]
  -- subst-node-unit-l (lf i) g (lift ())
  -- subst-node-unit-l (nd (f , ϕ)) ._ (inl idp) =
  --   ↓-ap-in (λ x → Node P x (_ , f)) (λ x → nd (f , x))
  --     (↓-Node-here-in P (Decor-== P (λ j p → subst-unit-l (ϕ j p))))
  -- subst-node-unit-l (nd (f , ϕ)) g (inr (k , p , n)) =
  --   ↓-ap-in (λ x → Node P x g) (λ x → nd (f , x))
  --     (↓-Node-there-in P (λ j p₁ → subst-unit-l (ϕ j p₁)) k p
  --       (subst-node-unit-l (ϕ k p) g n))

  -- --
  -- --  Unit right law
  -- -- 

  -- subst-unit-r-lem : {i : I} (w : W P i)
  --   → (j : I) (t : Σ I (λ k → Σ (Leaf P w k) (λ l → k == j)))
  --   → graft-unit-lf-to P w j (graft-leaf-to P w (λ k _ → lf k) j t)
  --     == transport (Leaf P w) (snd (snd t)) (fst (snd t))
  -- subst-unit-r-lem (lf i) .i (.i , idp , idp) = idp
  -- subst-unit-r-lem (nd (f , ϕ)) j (.j , (k , p , l) , idp) =
  --   ap (λ x → (k , p , x)) (subst-unit-r-lem (ϕ k p) j (j , l , idp))

  -- subst-unit-r-frm : {i : I} {f : Op P i}
  --   → (κ : (g : Ops P) → Node P (corolla P f) g → InFrame P g)
  --   → snd (κ (i , f) (inl idp))
  --       == (λ j → corolla-frm P f j ∘e (subst-leaf-eqv (corolla P f) κ j) ⁻¹)
  --            [ (λ x → Frame P x f) ↓ graft-unit P (fst (κ (i , f) (inl idp))) ]
  -- subst-unit-r-frm {i} {f} κ = 
  --   let (w , α) = κ (i , f) (inl idp)
  --       ψ k _ = lf k
  --       t j l = graft-leaf-from P w ψ j l
        
  --       lem j l = –> (α j) (graft-unit-lf-to P w j l)
  --                   =⟨ ! (graft-leaf-to-from P w ψ j l) |in-ctx (λ x → –> (α j) (graft-unit-lf-to P w j x)) ⟩
  --                 –> (α j) (graft-unit-lf-to P w j (graft-leaf-to P w ψ j (t j l)))
  --                   =⟨ subst-unit-r-lem w j (t j l) |in-ctx (–> (α j)) ⟩
  --                 –> (α j) (transport (Leaf P w) (snd (snd (t j l))) (fst (snd (t j l))))
  --                   =⟨ transp-→ (Leaf P w) (Param P f) (snd (snd (t j l))) (λ i → –> (α i)) ⟩ 
  --                 –> (corolla-frm P f j) (subst-leaf-from (corolla P f) κ j l) ∎

  --   in graft-unit-frm P w α ∙'ᵈ (λ= λ j → equiv-== (λ l → lem j l))

  -- --
  -- --  Associativity of substitution
  -- -- 

  -- subst-assoc : {i : I} (w : W P i) 
  --   → (κ : (g : Ops P) → Node P w g → InFrame P g) 
  --   → (ν : (g : Ops P) → Σ (Ops P) (λ k → Σ (Node P w k) (λ p → Node P (fst (κ k p)) g)) → InFrame P g)
  --   → subst w (λ g n → subst-γ _ (κ g n) (λ g' n' → ν g' (g , n , n')))
  --     == subst (subst w κ) (λ g n → ν g (subst-node-from w κ g n))
  -- subst-assoc (lf i) κ ν = idp
  -- subst-assoc (nd (f , ϕ)) κ ν = 
  --   let (w , α) = κ (_ , f) (inl idp)

  --       -- induction hypothesis
  --       κ' j p g n = κ g (inr (j , p , n))
  --       ν' j p g t = ν g (fst t , (inr (j , p , fst (snd t))) , snd (snd t))
  --       α' j = α j ∘e (subst-leaf-eqv w (λ g' n' → ν g' ((_ , f) , inl idp , n')) j) ⁻¹
  --       ih j p = subst-assoc (ϕ j p) (κ' j p) (ν' j p) 

  --       -- arguments for subst-graft
  --       κ-sg g n = ν g ((_ , f) , inl idp , n)
  --       ψ-sg j l = subst (ϕ j (–> (α j) l)) (κ' j (–> (α j) l))
  --       θ-sg g t = let (j , l , n) = t
  --                  in ν' j (–> (α j) l) g (subst-node-from (ϕ j (–> (α j) l)) (κ' j (–> (α j) l)) g n)

  --       -- Decoration fixup ...
  --       θ' g t = let (j , l₀ , n) = t
  --                    (k , l₁ , n') = subst-node-from (ϕ j (–> (α j) l₀)) (κ' j (–> (α j) l₀)) g n
  --                in k , inr (j , –> (α j) l₀ , l₁) , n'
                 
  --       lem g n = ⊔-codiag (λ n → (_ , f) , inl idp , n) (θ' g) (ν g) (graft-node-from P w ψ-sg g n)
        
  --   in ap (graft P (subst w κ-sg)) (Decor-== (Fr P) (λ j l → ih j (–> (α' j) l))) ∙ 
  --      subst-graft w ψ-sg κ-sg θ-sg ∙
  --      ap (subst (graft P w ψ-sg)) (λ= (λ g → λ= (λ n → lem g n)))

  -- postulate
  
  --   subst-assoc-lf-po : {i : I} (w : W P i) 
  --     → (κ : (g : Ops P) → Node P w g → InFrame P g)
  --     → (ν : (g : Ops P) → Σ (Ops P) (λ h → Σ (Node P w h) (λ n → Node P (fst (κ h n)) g)) → InFrame P g)
  --     → (j : I) (l : Leaf P w j)
  --     → subst-lf-to {w = w} l == subst-lf-to {w = subst w κ} (subst-lf-to {w = w} l) [ (λ x → Leaf P x j) ↓ subst-assoc w κ ν ] 
  --   -- subst-assoc-lf-po (lf i) κ ν .i idp = idp
  --   -- subst-assoc-lf-po (nd (f , ϕ)) κ ν j (k , p , l) = 
  --   --   let (w , α) = κ (_ , f) (inl idp)

  --   --       -- induction hypothesis
  --   --       κ' j p g n = κ g (inr (j , p , n))
  --   --       ν' j p g t = ν g (fst t , (inr (j , p , fst (snd t))) , snd (snd t))
  --   --       α' j = α j ∘e (subst-leaf-eqv w (λ g' n' → ν g' ((_ , f) , inl idp , n')) j) ⁻¹
  --   --       ih j p = subst-assoc (ϕ j p) (κ' j p) (ν' j p) 

  --   --       -- arguments for subst-graft
  --   --       κ-sg g n = ν g ((_ , f) , inl idp , n)
  --   --       ψ-sg j l = subst (ϕ j (–> (α j) l)) (κ' j (–> (α j) l))

  --   --       ih-po : subst-lf-to l == subst-lf-to (subst-lf-to l) [ (λ x → Leaf P x j) ↓ subst-assoc (ϕ k p) (κ' k p) (ν' k p) ]
  --   --       ih-po = subst-assoc-lf-po (ϕ k p) (κ' k p) (ν' k p) j l

  --   --       my-κ g n = subst-γ _ (κ g n) (λ g' n' → ν g' (g , n , n'))
  --   --       my-ν g n = ν g (subst-node-from (nd (f , ϕ)) κ g n)
  --   --       pth₀ = ap (graft P (subst w κ-sg)) (Decor-== (Fr P) (λ j l → ih j (–> (α' j) l)))

  --   --       Q x =  Leaf P (subst (ϕ k x) (λ g n → my-κ g (inr (k , x , n)))) j 
  --   --       Q' x = Leaf P (subst (subst (ϕ k x) (κ' k x)) (λ g n → ν' k x g (subst-node-from (ϕ k x) (κ' k x) g n))) j 

  --   --       l' = <– (α' k) p
  --   --       p' = –> (α' k) l'
  --   --       l₀ = transport! Q (<–-inv-r (α' k) p) (subst-lf-to {w = ϕ k p} l)
  --   --       l₁ = transport! Q' (<–-inv-r (α' k) p) (subst-lf-to {w = subst (ϕ k p) (κ' k p)} (subst-lf-to {w = ϕ k p} l))

  --   --       pth-ovr₀ : graft-lf-to P {w = subst w κ-sg} (k , l' , l₀)
  --   --         == graft-lf-to P {w = subst w κ-sg} (k , l' , l₁)
  --   --           [ (λ x → Leaf P (graft P (subst w κ-sg) x) j) ↓ Decor-== (Fr P) (λ j l → ih j (–> (α' j) l)) ]
  --   --       pth-ovr₀ = ↓-graft-Leaf-ih P (λ j₁ l₁ → ih j₁ (–> (α' j₁) l₁)) k l' {!!}

  --   --       pth-ovr₁ : graft-lf-to P {w = subst w κ-sg} (k , l' , l₀)
  --   --         == graft-lf-to P {w = subst w κ-sg} (k , l' , l₁) [ (λ x → Leaf P x j) ↓ pth₀ ]
  --   --       pth-ovr₁ = ↓-ap-in (λ x → Leaf P x j) (graft P (subst w κ-sg)) pth-ovr₀ 

  --   --   in pth-ovr₁ ∙ᵈ {!!}

  -- subst-assoc-frm : {i : I} {f : Op P i}
  --   → (w : W P i) (α : Frame P w f)
  --   → (κ : (g : Ops P) → Node P w g → InFrame P g)
  --   → (ν : (g : Ops P) → Σ (Ops P) (λ h → Σ (Node P w h) (λ n → Node P (fst (κ h n)) g)) → InFrame P g)
  --   → (λ j → α j ∘e subst-leaf-eqv w (λ g n → subst-γ g (κ g n) (λ g₁ n₁ → ν g₁ (g , n , n₁))) j ⁻¹) == 
  --     (λ j → (α j ∘e subst-leaf-eqv w κ j ⁻¹) ∘e subst-leaf-eqv (subst w κ) (λ g n → ν g (<– (subst-node-eqv w κ g) n)) j ⁻¹)
  --       [ (λ x → Frame P x f) ↓ subst-assoc w κ ν ]                          
  -- subst-assoc-frm w α κ ν =
  --   let κ' g n = subst-γ g (κ g n) (λ g₁ n₁ → ν g₁ (g , n , n₁))
  --       ν' g n = ν g (<– (subst-node-eqv w κ g) n)
  --       lem j l₀ l₁ q = subst-leaf-from w κ' j l₀
  --                         =⟨ ! (subst-lf-from-to {w = w} (subst-lf-from {w = w} {κ = κ'} l₀)) ⟩ 
  --                       subst-lf-from {w = w} {κ = κ} (subst-lf-to {w = w} {κ = κ} (subst-lf-from {w = w} {κ = κ'} l₀))
  --                         =⟨ ! (ap (subst-lf-from {w = w}) (subst-lf-from-to {w = subst w κ} (subst-lf-to {w = w} (subst-lf-from {w = w} l₀)))) ⟩
  --                       subst-lf-from {w = w} {κ = κ} (subst-lf-from {w = subst w κ} {κ = ν'}
  --                         (subst-lf-to {w = subst w κ} {κ = ν'} (subst-lf-to {w = w} {κ = κ} (subst-lf-from {w = w} {κ = κ'} l₀))))
  --                         =⟨ ! (to-transp (subst-assoc-lf-po w κ ν j (subst-lf-from {w = w} l₀)))
  --                           |in-ctx (λ x → subst-lf-from {w = w} (subst-lf-from {w = subst w κ} x)) ⟩ 
  --                       subst-lf-from {w = w} (subst-lf-from {w = subst w κ}
  --                         (transport (λ x → Leaf P x j) (subst-assoc w κ ν) (subst-lf-to (subst-lf-from {w = w} l₀)))) 
  --                         =⟨ subst-lf-to-from {w = w} l₀ |in-ctx (λ x → subst-lf-from {w = w} (subst-lf-from {w = subst w κ}
  --                              (transport (λ x → Leaf P x j) (subst-assoc w κ ν) x))) ⟩ 
  --                       subst-lf-from {w = w} (subst-lf-from {w = subst w κ} (transport (λ x → Leaf P x j) (subst-assoc w κ ν) l₀)) 
  --                         =⟨ to-transp q |in-ctx (λ x → subst-lf-from {w = w} (subst-lf-from {w = subst w κ} x)) ⟩ 
  --                       subst-lf-from {w = w} (subst-lf-from {w = subst w κ} l₁) ∎
  --   in ↓-W-Frame-in P (λ j l₀ l₁ q → ap (–> (α j)) (lem j l₀ l₁ q)) 

  -- postulate
  
  --   subst-node-assoc : {i : I} {f : Op P i}
  --     → (w : W P i) (α : Frame P w f)
  --     → (κ : (g : Ops P) → Node P w g → InFrame P g)
  --     → (ν : (g : Ops P) → Σ (Ops P) (λ h → Σ (Node P w h) (λ n → Node P (fst (κ h n)) g)) → InFrame P g)
  --     → (g h : Ops P) (m : Node P w h) (k : Ops P) (n : Node P (fst (κ h m)) k) (o : Node P (fst (ν k (h , m , n))) g)
  --     → subst-node-to w (λ g₁ n₁ → subst-γ g₁ (κ g₁ n₁) (λ g' n' → ν g' (g₁ , n₁ , n')))
  --                   g (h , m , subst-node-to (fst (κ h m)) (λ g' n' → ν g' (h , m , n')) g (k , n , o))
  --         == subst-node-to (subst w κ) (λ g₁ n₁ → ν g₁ (subst-node-from w κ g₁ n₁))
  --              g (k , subst-node-to w κ k (h , m , n) , transport! (λ x → Node P (fst (ν k x)) g) (<–-inv-l (subst-node-eqv w κ k) (h , m , n)) o)
  --           [ (λ x → Node P x g) ↓ subst-assoc w κ ν ]
  --   -- subst-node-assoc = {!!}

  -- record SubstRelLaws (SRel : SubstRel) : Type ℓ where
  --   field

  --     subst-unit-l-rel : {i : I} {f : Op P i}
  --       → (w : W P i) (α : Frame P w f) (r : R (i , f) (w , α))
  --       → γ-rel SRel (i , f) (w , α) r (λ g _ → η (SubstBiasedMgm SRel) g)
  --           == r [ R (i , f) ↓ pair= (subst-unit-l w) (subst-unit-l-frm w α) ]

  --     subst-unit-r-rel : {i : I} {f : Op P i}
  --       → (κ : (g : Ops P) → Node P (corolla P f) g → Op (P // R) g)
  --       → snd (κ (i , f) (inl idp)) == γ-rel SRel (i , f) (corolla P f , corolla-frm P f) (η-rel SRel (i , f)) κ
  --           [ R (i , f) ↓ pair= (graft-unit P (fst (fst ((κ (i , f) (inl idp)))))) (subst-unit-r-frm (λ g n → fst (κ g n))) ]

  --     subst-assoc-rel : {i : I} {f : Op P i}
  --       → (w : W P i) (α : Frame P w f) (r : R (i , f) (w , α))
  --       → (κ : (g : Ops P) → Node P w g → Op (P // R) g)
  --       → (ν : (g : Ops P) → Σ (Ops P) (λ h → Σ (Node P w h) (λ n → Node P (fst (fst (κ h n))) g)) → Op (P // R) g)
  --       → let κ' g n = fst (κ g n)
  --             ν' g t = fst (ν g t)
  --         in γ-rel SRel (i , f) (w , α) r (λ g n → subst-γ g (κ' g n) (λ g₁ n₁ → ν' g₁ (g , n , n₁)) ,
  --                                                  γ-rel SRel g (κ' g n) (snd (κ g n)) (λ g₁ n₁ → ν g₁ (g , n , n₁)))
  --            == γ-rel SRel (i , f) (subst-γ (i , f) (w , α) κ')
  --                                  (γ-rel SRel (i , f) (w , α) r κ)
  --                                  (λ g n → ν g (<– (subst-node-eqv w κ' g) n))
  --              [ R (i , f) ↓ pair= (subst-assoc w κ' ν') (subst-assoc-frm w α κ' ν') ]


  -- open SubstRelLaws

  -- SubstBiasedLaws : (SRel : SubstRel) (SLaws : SubstRelLaws SRel)
  --   → BiasedLaws (P // R) (SubstBiasedMgm SRel)
  -- unit-l (SubstBiasedLaws SRel SLaws) ((w , α) , r) =
  --   pair= (pair= (subst-unit-l w) (subst-unit-l-frm w α))
  --         (subst-unit-l-rel SLaws w α r)
  -- unit-r (SubstBiasedLaws SRel SLaws) {i , f} κ =
  --   let ((w , α) , r) = κ (i , f) (inl idp)
  --       κ' g n = fst (κ g n)
  --   in pair= (pair= (graft-unit P w) (subst-unit-r-frm κ'))
  --            (subst-unit-r-rel SLaws κ)
  -- assoc (SubstBiasedLaws SRel SLaws) {i , f} ((w , α) , r) κ ν = 
  --   let κ' g n = fst (κ g n)
  --       ν' g t = fst (ν g t)
  --   in pair= (pair= (subst-assoc w κ' ν') (subst-assoc-frm w α κ' ν'))
  --            (subst-assoc-rel SLaws w α r κ ν)
  -- unit-l-frm (SubstBiasedLaws SRel SLaws) ((w , α) , r) g n =
  --   ↓-Σ-weaken (λ x → Node P (fst x) g)
  --     (↓-Σ-weaken (λ x → Node P x g)
  --                 (subst-node-unit-l w g n))
  -- unit-r-frm (SubstBiasedLaws SRel SLaws) {i , f} κ g n =
  --   ↓-Σ-weaken (λ x → Node P (fst x) g)
  --     (↓-Σ-weaken (λ x → Node P x g)
  --       (graft-unit-nd P (fst (fst (κ (_ , f) (inl idp)))) g n)) 
  -- assoc-frm (SubstBiasedLaws SRel SLaws) ((w , α) , r) κ ν g h m k n o =
  --   let κ' g n = fst (κ g n)
  --       ν' g t = fst (ν g t)
  --   in ↓-Σ-weaken (λ x → Node P (fst x) g)
  --        (↓-Σ-weaken (λ x → Node P x g)
  --                    (subst-node-assoc w α κ' ν' g h m k n o))

