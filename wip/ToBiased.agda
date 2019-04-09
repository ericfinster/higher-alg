{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial

-- This module needs to be rewritten for the new organizational setup ...
module wip.ToBiased where

  -- In the following we show that given a PolyMagma we can obtain a biased magma satisfying the biased laws 
  module _ {ℓ} {I : Type ℓ} {P : Poly I} (Mgm : PolyMagma P) (laws : SubInvar ⟪ Mgm ⟫ ) where

    open BiasedMgm
    open BiasedLaws
  
    biased-mgm : BiasedMgm P
    η     biased-mgm i     = μ Mgm (lf i)
    η-frm biased-mgm i     = μ-frm Mgm (lf i)
    γ     biased-mgm f ϕ   = μ Mgm (nd (f , λ j l → corolla P (ϕ j l)))
    γ-frm biased-mgm f ϕ j = (μ-frm Mgm w j) ∘e equiv (λ { (k , p , q) → (k , p , (j , q , idp)) }) (λ { (k , p , (_ , q , idp)) → (k , p , q)}) (λ { (_ , _ , (_ , _ , idp)) → idp}) (λ _ → idp)
      where 
        w = nd (f , λ k l → corolla P (ϕ k l))

    module left-laws {i : I} (f : Op P i) where

      w : W P i
      w = nd (f , λ j _ → corolla P (η biased-mgm j))

      pd : W (P // ⟪ Mgm ⟫) (i , μ Mgm w)
      pd = nd (((w , μ-frm Mgm _) , pair= idp idp) , κ)
        where κ : (g : Ops P) (n : Node P w g) → W (P // ⟪ Mgm ⟫) g
              κ g (inl idp) = lf g
              κ g (inr (_ , _ , inl idp)) = corolla (P // ⟪ Mgm ⟫) ((lf (fst g) , μ-frm Mgm _), pair= idp idp) 
              κ g (inr (_ , _ , inr ()))

      lem : (μ Mgm w , flatn-frm ⟪ Mgm ⟫ pd) == (f , flatn-frm ⟪ Mgm ⟫ (lf (_ , f)))
      lem = ! (laws pd) ∙ laws (lf (_ , f))

      unit-l-law : γ biased-mgm f (λ j _ → η biased-mgm j) == f
      unit-l-law = fst= lem

      unit-l-frm-law : (j : I) (p : Param P f j)
        → γ-frm-to biased-mgm (j , p , –> (η-frm biased-mgm j j) idp) == p [ (λ x → Param P x j) ↓ unit-l-law ]
      unit-l-frm-law j p = apd (λ { (_ , fr) → –> (fr j) (j , p , idp) }) lem
        >> ↓-ap-in (λ x → Param P x j) fst

    module right-laws {i : I} (ϕ : (j : I) → Param P (η biased-mgm i) j → Op P j) where

      w : W P i
      w = nd (η biased-mgm i , λ j p → corolla P (ϕ j p))

      f = ϕ i (–> (η-frm biased-mgm i i) idp)

      pd : W (P // ⟪ Mgm ⟫) (i , μ Mgm w)
      pd = nd (((w , μ-frm Mgm _) , pair= idp idp) , κ)
        where κ : (g : Ops P) (n : Node P w g) → W (P // ⟪ Mgm ⟫) g
              κ g (inl idp) = corolla (P // ⟪ Mgm ⟫) ((lf (fst g) , μ-frm Mgm _), pair= idp idp)
              κ g (inr (_ , _ , inl idp)) = lf g
              κ g (inr (_ , _ , inr ()))
      
      lem : (f , flatn-frm ⟪ Mgm ⟫ (lf (_ , f))) == (μ Mgm w , flatn-frm ⟪ Mgm ⟫ pd)
      lem = ! (laws (lf (_ , f))) ∙ (laws pd)

      unit-r-law : ϕ i (–> (η-frm biased-mgm i i) idp) == γ biased-mgm (η biased-mgm i) ϕ
      unit-r-law = fst= lem

      unit-r-frm-law : (j : I) (p : Param P (ϕ i (–> (η-frm biased-mgm i i) idp)) j)
        → p == γ-frm-to biased-mgm (i , –> (η-frm biased-mgm i i) idp , p) [ (λ x → Param P x j) ↓ unit-r-law ]
      unit-r-frm-law j p = apd (λ { (_ , fr) → –> (fr j) (j , p , idp) }) lem
        >> ↓-ap-in (λ x → Param P x j) fst

    module assoc-laws
      {i : I}
      (f : Op P i)
      (ϕ : (j : I) → Param P f j → Op P j)
      (ψ : (j : I) → Σ I (λ k → Σ (Param P f k) (λ p → Param P (ϕ k p) j)) → Op P j) where 
     
      -- left case
      lhs = γ biased-mgm (γ biased-mgm f ϕ) (λ k q → ψ k (_ , _ , γ-frm-snd-param biased-mgm q))

      left-w = nd (γ biased-mgm f ϕ , λ k q → corolla P (ψ k (_ , _ , γ-frm-snd-param biased-mgm q)))
          
      left-nd₁ = corolla (P // ⟪ Mgm ⟫) ((nd (f , λ j p → corolla P (ϕ j p)) , μ-frm Mgm _) , pair= idp idp)

      left-κ : (f : Ops P) (n : Node P left-w f) → W (P // ⟪ Mgm ⟫) f
      left-κ _ (inl idp)               = left-nd₁
      left-κ _ (inr (k , q , inl idp)) = lf (k , ψ k (_ , _ , γ-frm-snd-param biased-mgm q))
      left-κ _ (inr (_ , _ , inr (_ , _ , ()))) 

      left-pd : W (P // ⟪ Mgm ⟫) (i , lhs)
      left-pd = nd (((left-w , μ-frm Mgm _) , pair= idp idp) , left-κ)

      -- right case
      rhs = γ biased-mgm f (λ j p → γ biased-mgm (ϕ j p) (λ k q → ψ k (_ , _ , q)))

      right-w = nd (f , λ j p → corolla P (γ biased-mgm (ϕ j p) (λ k q → ψ k (_ , _ , q))))
                                                                                    
      right-nd : (j : I) → (p : Param P f j) → W (P // ⟪ Mgm ⟫) (j , _)
      right-nd j p  = corolla (P // ⟪ Mgm ⟫) ((nd (ϕ j p , λ k q → corolla P (ψ k (_ , _ , q))) , μ-frm Mgm _) , pair= idp idp)

      right-κ : (f : Ops P) (n : Node P right-w f) → W (P // ⟪ Mgm ⟫) f 
      right-κ _ (inl idp)               = lf (_ , f)
      right-κ _ (inr (j , p , inl idp)) = right-nd j p
      right-κ _ (inr (_ , _ , inr (_ , _ , ()))) 

      right-pd : W (P // ⟪ Mgm ⟫) (i , rhs)
      right-pd = nd (((right-w , μ-frm Mgm _) , pair= idp idp) , right-κ)          

      -- flatn lhs = flatn rhs

      lem-ψ :
        (λ (j : I)
           (p : Param P f j)
           (k : I)
           (q : Param P (ϕ j p) k)
           → ((j , p , q) , λ (l : I) (r : Param P (ψ k (j , p , q)) l) → r))
        ==
        (λ (j : I)
           (p : Param P f j)
           (k : I)
           (q : Param P (ϕ j p) k)
           → (γ-frm-from biased-mgm (γ-frm-to biased-mgm (j , p , q)) , λ (l : I) (r : Param P (ψ k (j , p , q)) l) → transport! (λ x → Param P (ψ k x) l) (<–-inv-l (γ-frm biased-mgm f ϕ k) (j , p , q)) r))
      lem-ψ = let pth j p k q = ↓-Π-cst-app-in  λ l → ↓-Π-cst-app-in λ r → !ᵈ (to-transp!!-↓ (λ x → Param P (ψ k x) l) (<–-inv-l (γ-frm biased-mgm f ϕ k) (j , p , q)) r)
        in λ= λ j → λ= λ p → λ= λ k → λ= λ q → pair= (! (<–-inv-l (γ-frm biased-mgm f ϕ k) (j , p , q))) (pth j p k q)

      -- Simple proof of assoc-flatn which doesn't rely on lem-ψ but not convenient to work with when we want to prove assoc-frm-law
      -- assoc-flatn : flatn ⟪ Mgm ⟫ right-pd == flatn ⟪ Mgm ⟫ left-pd
      -- assoc-flatn = ap (λ x → nd (f , x)) (λ= λ j → λ= λ p → ap (λ y → nd (ϕ j p , y)) (λ= λ m → λ= λ q → ap (λ { (j' , p' , q') → corolla P (ψ m (j' , p' , q')) }) (! (<–-inv-l (γ-frm biased-mgm f ϕ m) (j , p , q)))))

      assoc-flatn : flatn ⟪ Mgm ⟫ right-pd == flatn ⟪ Mgm ⟫ left-pd
      assoc-flatn = ap (λ g → nd (f , λ j p → nd (ϕ j p , λ k q → corolla P (ψ k (fst (g j p k q)))))) lem-ψ

      lem : (rhs , flatn-frm ⟪ Mgm ⟫ right-pd) == (lhs , flatn-frm ⟪ Mgm ⟫ left-pd) [ OutFrame P ↓ assoc-flatn ]
      lem = ! (laws right-pd) ∙ᵈ apd (λ x → (μ Mgm x , μ-frm Mgm x)) assoc-flatn ∙ᵈ (laws left-pd)
        >> transport (λ x → (rhs , flatn-frm ⟪ Mgm ⟫ right-pd) == (lhs , flatn-frm ⟪ Mgm ⟫ left-pd) [ OutFrame P ↓ x ]) (∙-unit-r assoc-flatn)

      -- Our magma is associative
      assoc-law : γ biased-mgm f (λ j p → γ biased-mgm (ϕ j p) (λ k q → ψ k (j , p , q))) == γ biased-mgm (γ biased-mgm f ϕ) (λ j p → ψ j (<– (γ-frm biased-mgm f ϕ j) p))
      assoc-law = ↓-cst-out (ap↓ fst lem) 

      -- The frames are coherent w.r.t. assoc
      assoc-frm-law :
        (l : I)
        (j : I) (p : Param P f j)
        (k : I) (q : Param P (ϕ j p) k)
        (r : Param P (ψ k (j , p , q)) l)
        → γ-frm-to biased-mgm (j , p , γ-frm-to biased-mgm (k , q , r)) ==
          γ-frm-to biased-mgm (k , γ-frm-to biased-mgm (j , p , q) , transport! (λ x → Param P (ψ k x) l) (<–-inv-l (γ-frm biased-mgm f ϕ k) (j , p , q)) r)
          [ (λ x → Param P x l) ↓ assoc-law ]
      assoc-frm-law l j p k q r = ↓-Π-out lf-to-par-pth lf-pth
        >> ↓-cst2-out _ _ 
        >> ↓-ap-in _ _
        >> transport (λ x → γ-frm-to biased-mgm (j , p , γ-frm-to biased-mgm (k , q , r)) == γ-frm-to biased-mgm (k , γ-frm-to biased-mgm (j , p , q) , transport! (λ x → Param P (ψ k x) l) (<–-inv-l (γ-frm biased-mgm f ϕ k) (j , p , q)) r) [ (λ x → Param P x l) ↓ x ]) (lem-ap-pair assoc-flatn lem)
        where kpq-r : Leaf P (flatn ⟪ Mgm ⟫ right-pd) l
              kpq-r = (j , p , (k , q , (l , r , idp)))

              kpq-l : Leaf P (flatn ⟪ Mgm ⟫ left-pd) l
              kpq-l = (j , p , (k , q , (l , transport! (λ x → Param P (ψ k x) l) (<–-inv-l (γ-frm biased-mgm f ϕ k) (j , p , q)) r , idp)))

              lf-to-par-pth : –> (flatn-frm ⟪ Mgm ⟫ right-pd l) == –> (flatn-frm ⟪ Mgm ⟫ left-pd l) [ (λ { (x , (y , z)) → Leaf P x l → Param P y l })  ↓ pair= assoc-flatn lem ]
              lf-to-par-pth = apd↓ (λ { (_ , fr) → –> (fr l)  }) lem

              lf-pth : kpq-r == kpq-l [ (λ { (x , _) → Leaf P x l}) ↓ pair= assoc-flatn lem ]
              lf-pth = apd (λ g → (j , p , (k , q , (l , snd (g j p k q) l r , idp)))) lem-ψ
                >> ↓-ap-in (λ x → Leaf P x l) (λ g → nd (f , λ j p → nd (ϕ j p , λ k q → corolla P (ψ k (fst (g j p k q))))))
                >> ↓-cst2-in assoc-flatn lem
                                         
              lem-ap-pair : ∀ {i j} {A B : Type i} {C : A → B → Type j}
                {x x' : A} (p : x == x')
                {y y' : B} {z : C x y} {z' : C x' y'}
                (q : (y , z) == (y' , z') [ (λ x → Σ B (C x)) ↓ p ])
                → ap (fst ∘ snd) (pair= p q) == ↓-cst-out (ap↓ fst q)
              lem-ap-pair idp idp = idp 
            

    -- Finally, we pack the laws altogether

    biased-mgm-laws : BiasedLaws P biased-mgm
    unit-l     biased-mgm-laws = unit-l-law
     where open left-laws
    unit-r     biased-mgm-laws = unit-r-law
      where open right-laws
    assoc      biased-mgm-laws = assoc-law
      where open assoc-laws
    unit-l-frm biased-mgm-laws = unit-l-frm-law
      where open left-laws
    unit-r-frm biased-mgm-laws = unit-r-frm-law
      where open right-laws
    assoc-frm  biased-mgm-laws = assoc-frm-law
      where open assoc-laws
