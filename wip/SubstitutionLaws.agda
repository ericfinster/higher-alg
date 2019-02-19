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

  --
  --  Commutation of substitution and grafting
  --

  postulate
  
    subst-graft : {i : I} (w : W P i) (ψ : (j : I) → Leaf P w j → W P j)
      → (κ : (g : Ops P) → Node P w g → InFrame P g)
      → (θ : (g : Ops P) → Σ I (λ j → Σ (Leaf P w j) (λ l → Node P (ψ j l) g)) → InFrame P g) 
      → graft P (subst w κ) (λ j l → subst (ψ j (subst-leaf-from w κ j l)) (λ g n → θ g (j , subst-leaf-from w κ j l , n)))
        == subst (graft P w ψ) (λ g n → ⊔-rec (κ g) (θ g) (graft-node-from P w ψ g n))                          
    -- subst-graft (lf i) ψ κ θ = idp
    -- subst-graft (nd (f , ϕ)) ψ κ θ = 
    --   let (w , α) = κ (_ , f) (inl idp)
    --       p j l₀ = –> (α j) l₀
    --       ψ' j l₀ k l₁ = ψ k (j , p j l₀ , l₁)
    --       κ' j l₀ g n = κ g (inr (j , p j l₀ , n))
    --       θ' j l₀ g trpl = let (k , l₁ , n) = trpl in θ g (k , (j , p j l₀ , l₁) , n)
    --       ψ₀ j l₀ = subst (ϕ j (p j l₀)) (κ' j l₀)
    --       slf k j l₀ l₁ = subst-leaf-from (ϕ j (p j l₀)) (κ' j l₀) k l₁
    --       ψ₁ k trpl = let (j , l₀ , l₁) = trpl in subst (ψ' j l₀ k (slf k j l₀ l₁)) (λ g n → θ' j l₀ g (k , slf k j l₀ l₁ , n))
    --   in graft P (graft P w ψ₀) (λ j l → ψ₁ j (graft-leaf-from P w ψ₀ j l))
    --        =⟨ graft-assoc P w ψ₀ ψ₁ ⟩
    --      graft P w (λ j l₀ → graft P (ψ₀ j l₀) (λ k l₁ → ψ₁ k (j , l₀ , l₁)))
    --        =⟨ ap (graft P w) (λ= (λ j → λ= (λ l₀ → subst-graft (ϕ j (p j l₀)) (ψ' j l₀) (κ' j l₀) (θ' j l₀) ∙
    --           ap (subst (graft P (ϕ j (p j l₀)) (ψ' j l₀))) (λ= (λ g → λ= (λ n →
    --             ⊔-rec-∘ (κ g) (θ g)
    --                 (λ l₁ → inr (j , p j l₀ , l₁))
    --                 (λ t → let (k , l₁ , n) = t in (k , (j , p j l₀ , l₁) , n))
    --                 (graft-node-from P (ϕ j (p j l₀)) (ψ' j l₀) g n))))))) ⟩ 
    --      subst (graft P (nd (f , ϕ)) ψ) (λ g n → ⊔-rec (κ g) (θ g) (graft-node-from P (nd (f , ϕ)) ψ g n)) ∎


    subst-graft-frm-lem : {i : I} (w : W P i) (ψ : (j : I) → Leaf P w j → W P j)
      → (κ : (g : Ops P) → Node P w g → InFrame P g)
      → (θ : (g : Ops P) → Σ I (λ j → Σ (Leaf P w j) (λ l → Node P (ψ j l) g)) → InFrame P g)
      → (j : I) (l : Leaf P (subst (graft P w ψ) (λ g n → ⊔-rec (κ g) (θ g) (graft-node-from P w ψ g n))) j)
      → Σ-fmap-r (λ i → λ { (l₀ , l₁) → subst-leaf-from w κ i l₀ , subst-leaf-from (ψ i (subst-leaf-from w κ i l₀)) (λ g n → θ g (i , subst-leaf-from w κ i l₀ , n)) j l₁ })
          (graft-leaf-from P (subst w κ) (λ j l → subst (ψ j (subst-leaf-from w κ j l)) (λ g n → θ g (j , subst-leaf-from w κ j l , n))) j (transport! (λ x → Leaf P x j) (subst-graft w ψ κ θ) l))
         == graft-leaf-from P w ψ j (subst-leaf-from (graft P w ψ) (λ g n → ⊔-rec (κ g) (θ g) (graft-node-from P w ψ g n)) j l) 

  --
  --  Associativity of substitution
  -- 

  subst-assoc : {i : I} (w : W P i) 
    → (κ : (g : Ops P) → Node P w g → InFrame P g) 
    → (ν : (g : Ops P) → Σ (Ops P) (λ k → Σ (Node P w k) (λ p → Node P (fst (κ k p)) g)) → InFrame P g)
    → subst w (λ g n → subst-γ _ (κ g n) (λ g' n' → ν g' (g , n , n')))
      == subst (subst w κ) (λ g n → ν g (subst-node-from w κ g n))
  subst-assoc (lf i) κ ν = idp
  subst-assoc (nd (f , ϕ)) κ ν = 
    let (w , α) = κ (_ , f) (inl idp)

        -- induction hypothesis
        κ' j p g n = κ g (inr (j , p , n))
        ν' j p g t = ν g (fst t , (inr (j , p , fst (snd t))) , snd (snd t))
        α' j = α j ∘e (subst-leaf-eqv w (λ g' n' → ν g' ((_ , f) , inl idp , n')) j) ⁻¹
        ih j p = subst-assoc (ϕ j p) (κ' j p) (ν' j p) 

        -- arguments for subst-graft
        κ-sg g n = ν g ((_ , f) , inl idp , n)
        ψ-sg j l = subst (ϕ j (–> (α j) l)) (κ' j (–> (α j) l))
        θ-sg g t = let (j , l , n) = t
                   in ν' j (–> (α j) l) g (subst-node-from (ϕ j (–> (α j) l)) (κ' j (–> (α j) l)) g n)

        -- Decoration fixup ...
        θ' g t = let (j , l₀ , n) = t
                     (k , l₁ , n') = subst-node-from (ϕ j (–> (α j) l₀)) (κ' j (–> (α j) l₀)) g n
                 in k , inr (j , –> (α j) l₀ , l₁) , n'
                 
        lem g n = ⊔-codiag (λ n → (_ , f) , inl idp , n) (θ' g) (ν g) (graft-node-from P w ψ-sg g n)
        
    in ap (graft P (subst w κ-sg)) (λ= (λ j → λ= λ l → ih j (–> (α' j) l))) ∙
       subst-graft w ψ-sg κ-sg θ-sg ∙
       ap (subst (graft P w ψ-sg)) (λ= (λ g → λ= (λ n → lem g n)))


  subst-assoc-lf-action : {i : I} (w : W P i) 
    → (κ : (g : Ops P) → Node P w g → InFrame P g) 
    → (ν : (g : Ops P) → Σ (Ops P) (λ k → Σ (Node P w k) (λ p → Node P (fst (κ k p)) g)) → InFrame P g)
    → (j : I) → Leaf P (subst w (λ g n → subst-γ _ (κ g n) (λ g' n' → ν g' (g , n , n')))) j
    → Leaf P (subst (subst w κ) (λ g n → ν g (subst-node-from w κ g n))) j
  subst-assoc-lf-action w κ ν j l = {!!}
  
  -- subst-assoc-frm-lem : {i : I} (w : W P i) 
  --   → (κ : (g : Ops P) → Node P w g → InFrame P g)
  --   → (ν : (g : Ops P) → Σ (Ops P) (λ h → Σ (Node P w h) (λ n → Node P (fst (κ h n)) g)) → InFrame P g)
  --   → (j : I) (l : Leaf P (subst (subst w κ) (λ g n → ν g (subst-node-from w κ g n))) j)
  --   → subst-leaf-from w (λ g n → subst-γ g (κ g n) (λ g₁ n₁ → ν g₁ (g , n , n₁))) j
  --                     (transport! (λ x → Leaf P x j) (subst-assoc w κ ν) l)
  --     == subst-leaf-from w κ j (subst-leaf-from (subst w κ) (λ g n → ν g (subst-node-from w κ g n)) j l)
  -- subst-assoc-frm-lem (lf i) κ ν .i idp = idp
  -- subst-assoc-frm-lem (nd (f , ϕ)) κ ν j l = 
  --   let (w , α) = κ (_ , f) (inl idp)

  --       -- induction hypothesis
  --       κ' k p g n = κ g (inr (k , p , n))
  --       ν' k p g t = ν g (fst t , (inr (k , p , fst (snd t))) , snd (snd t))
  --       α' k = α k ∘e (subst-leaf-eqv w (λ g' n' → ν g' ((_ , f) , inl idp , n')) k) ⁻¹
  --       ih k p = subst-assoc-frm-lem (ϕ k p) (κ' k p) (ν' k p)
        
  --   in {!ih!}

  -- subst-leaf-from : {i : I} (w : W P i)
  --   → (κ : (g : Ops P) → Node P w g → InFrame P g)
  --   → (j : I) → Leaf P (subst w κ) j → Leaf P w j
  -- subst-leaf-from (lf i) κ j l = l
  -- subst-leaf-from (nd (f , ϕ)) κ j l = 
  --   let (w , α) = κ (_ , f) (inl idp)
  --       κ' j l g n = κ g (inr (j , –> (α j) l , n))
  --       ψ j l = subst (ϕ j (–> (α j) l)) (κ' j l)
  --       (k , l₀ , l₁) = graft-leaf-from P w ψ j l
  --   in k , –> (α k) l₀ , subst-leaf-from (ϕ k (–> (α k) l₀)) (κ' k l₀) j l₁

  postulate
  
    subst-assoc-frm : {i : I} {f : Op P i}
      → (w : W P i) (α : Frame P w f)
      → (κ : (g : Ops P) → Node P w g → InFrame P g)
      → (ν : (g : Ops P) → Σ (Ops P) (λ h → Σ (Node P w h) (λ n → Node P (fst (κ h n)) g)) → InFrame P g)
      → (λ j → α j ∘e subst-leaf-eqv w (λ g n → subst-γ g (κ g n) (λ g₁ n₁ → ν g₁ (g , n , n₁))) j ⁻¹) == 
        (λ j → (α j ∘e subst-leaf-eqv w κ j ⁻¹) ∘e subst-leaf-eqv (subst w κ) (λ g n → ν g (<– (subst-node-eqv w κ g) n)) j ⁻¹)
          [ (λ x → Frame P x f) ↓ subst-assoc w κ ν ]                          
    -- subst-assoc-frm w α κ ν =
    --   ↓-W-Frame-in P (λ j l₀ l₁ q → 
    --     ap (–> (α j)) {!!}) --(subst-assoc-frm-lem w κ ν j l₀ l₁ q)

    subst-node-assoc : {i : I} {f : Op P i}
      → (w : W P i) (α : Frame P w f)
      → (κ : (g : Ops P) → Node P w g → InFrame P g)
      → (ν : (g : Ops P) → Σ (Ops P) (λ h → Σ (Node P w h) (λ n → Node P (fst (κ h n)) g)) → InFrame P g)
      → (g h : Ops P) (m : Node P w h) (k : Ops P) (n : Node P (fst (κ h m)) k) (o : Node P (fst (ν k (h , m , n))) g)
      → subst-node-to w (λ g₁ n₁ → subst-γ g₁ (κ g₁ n₁) (λ g' n' → ν g' (g₁ , n₁ , n')))
                    g (h , m , subst-node-to (fst (κ h m)) (λ g' n' → ν g' (h , m , n')) g (k , n , o))
          == subst-node-to (subst w κ) (λ g₁ n₁ → ν g₁ (subst-node-from w κ g₁ n₁))
               g (k , subst-node-to w κ k (h , m , n) , transport! (λ x → Node P (fst (ν k x)) g) (<–-inv-l (subst-node-eqv w κ k) (h , m , n)) o)
            [ (λ x → Node P x g) ↓ subst-assoc w κ ν ]
    -- subst-node-assoc = {!!}

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

