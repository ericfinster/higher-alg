{-# OPTIONS --without-K --rewriting --no-termination-check #-}

open import HoTT
open import Util
open import Polynomial

-- The postulates here can all be proved (see previous incarnations of
-- this library), however, they tend to seriously bog down typechecking.
-- Since we thus want to abstract them anyway, we leave them as
-- postulates here.

module Substitution {ℓ} {I : Type ℓ} {P : Poly I} (R : Relator P) where

  --
  --  Flattening 
  --

  flatten : {i : I} {f : Op P i} (pd : W (P // R) (i , f)) → W P i

  flatten-leaf-in : {i : I} {f : Op P i} (pd : W (P // R) (i , f))
    → (j : I) → Param P f j → Leaf P (flatten pd) j 

  flatten-leaf-elim : ∀ {ℓ'} {i : I} {f : Op P i}
    → (pd : W (P // R) (i , f)) (j : I)
    → (Q : Leaf P (flatten pd) j → Type ℓ')
    → (σ : (p : Param P f j) → Q (flatten-leaf-in pd j p))
    → (l : Leaf P (flatten pd) j) → Q l

  flatten-leaf-elim-β : ∀ {ℓ'} {i : I} {f : Op P i}
    → (pd : W (P // R) (i , f)) (j : I)
    → (Q : Leaf P (flatten pd) j → Type ℓ')
    → (σ : (p : Param P f j) → Q (flatten-leaf-in pd j p))
    → (p : Param P f j)
    → flatten-leaf-elim pd j Q σ (flatten-leaf-in pd j p) == σ p

  -- flatten-frm-to : {i : I} {f : Op P i}
  --   → (pd : W (P // R) (i , f))
  --   → (j : I) → Leaf P (flatten pd) j → Param P f j

  -- flatten-frm-from : {i : I} {f : Op P i}
  --   → (pd : W (P // R) (i , f))
  --   → (j : I) → Param P f j → Leaf P (flatten pd) j 

  -- postulate
  
  --   flatten-frm-to-from : {i : I} {f : Op P i}
  --     → (pd : W (P // R) (i , f))
  --     → (j : I) (p : Param P f j)
  --     → flatten-frm-to pd j (flatten-frm-from pd j p) == p

  --   flatten-frm-from-to : {i : I} {f : Op P i}
  --     → (pd : W (P // R) (i , f))
  --     → (j : I) (l : Leaf P (flatten pd) j )
  --     → flatten-frm-from pd j (flatten-frm-to pd j l) == l

  -- -- The flattened tree has a canonical c-frame
  -- flatten-frm : {i : I} {f : Op P i}
  --   → (pd : W (P // R) (i , f))
  --   → (j : I) → Leaf P (flatten pd) j ≃ Param P f j

  --
  --  Substitution
  --

  substitute : {i : I} (w : W P i)
    → (κ : (g : Ops P) → Node P w g → W (P // R) g)
    → W P i

  substitute-leaf-in : {i : I} (w : W P i)
    → (κ : (g : Ops P) → Node P w g → W (P // R) g)
    → ∀ j → Leaf P w j → Leaf P (substitute w κ) j

  substitute-leaf-elim : ∀ {ℓ'} {i : I} (w : W P i)
    → (κ : (g : Ops P) → Node P w g → W (P // R) g) (j : I)
    → (Q : Leaf P (substitute w κ) j → Type ℓ')
    → (σ : (l : Leaf P w j) → Q (substitute-leaf-in w κ j l))
    → (l : Leaf P (substitute w κ) j) → Q l

  substitute-leaf-elim-β : ∀ {ℓ'} {i : I} (w : W P i)
    → (κ : (g : Ops P) → Node P w g → W (P // R) g) (j : I)
    → (Q : Leaf P (substitute w κ) j → Type ℓ')
    → (σ : (l : Leaf P w j) → Q (substitute-leaf-in w κ j l))
    → (l : Leaf P w j)
    → substitute-leaf-elim w κ j Q σ (substitute-leaf-in w κ j l) == σ l
    
  -- substitute-lf-to : {i : I} (w : W P i)
  --   → (κ : (c : Σ I (Op P)) → Node P w (snd c) → W (P // R) c)
  --   → (j : I) → Leaf P (substitute w κ) j → Leaf P w j

  -- substitute-lf-from : {i : I} (w : W P i)
  --   → (κ : (c : Σ I (Op P)) → Node P w (snd c) → W (P // R) c)
  --   → (j : I) → Leaf P w j → Leaf P (substitute w κ) j 

  -- postulate
  
  --   substitute-lf-to-from : {i : I} (w : W P i)
  --     → (κ : (c : Σ I (Op P)) → Node P w (snd c) → W (P // R) c)
  --     → (j : I) (l : Leaf P w j)
  --     → substitute-lf-to w κ j (substitute-lf-from w κ j l) == l

  --   substitute-lf-from-to : {i : I} (w : W P i)
  --     → (κ : (c : Σ I (Op P)) → Node P w (snd c) → W (P // R) c)
  --     → (j : I) (l : Leaf P (substitute w κ) j)
  --     → substitute-lf-from w κ j (substitute-lf-to w κ j l) == l

  -- -- A substituted tree has the same leaves
  -- substitute-lf-eqv : {i : I} (w : W P i)
  --   → (κ : (c : Σ I (Op P)) → Node P w (snd c) → W (P // R) c)
  --   → (j : I) → Leaf P (substitute w κ) j ≃ Leaf P w j

  --
  --  Implementation
  --

  flatten (lf (i , f)) = corolla P f
  flatten (nd ((w , α , r) , κ)) = substitute w κ

  flatten-leaf-in (lf (i , f)) j p = j , p , idp
  flatten-leaf-in (nd ((w , α , r) , κ)) j p =
    substitute-leaf-in w κ j (<– (α j) p) 

  flatten-leaf-elim (lf (i , f)) j Q σ (.j , p , idp) = σ p
  flatten-leaf-elim (nd ((w , α , r) , κ)) j Q σ l₀ =
    let σ' l = transport (λ x → Q (substitute-leaf-in w κ j x)) (<–-inv-l (α j) l) (σ (–> (α j) l))
    in substitute-leaf-elim w κ j Q σ' l₀

  flatten-leaf-elim-β (lf (i , f)) j Q σ p = idp
  flatten-leaf-elim-β (nd ((w , α , r) , κ)) j Q σ p =
    let σ' l = transport (λ x → Q (substitute-leaf-in w κ j x)) (<–-inv-l (α j) l) (σ (–> (α j) l))
    in substitute-leaf-elim-β w κ j Q σ' (<– (α j) p) ∙ {!!} 

  -- flatten-frm-to (lf _) j (_ , p , idp) = p
  -- flatten-frm-to (nd ((w , α , r) , κ)) j l = –> (α j) (substitute-lf-to w κ j l)
  
  -- flatten-frm-from (lf (i , f)) j p = (j , p , idp)
  -- flatten-frm-from (nd ((w , α , r) , κ)) j p = substitute-lf-from w κ j (<– (α j) p)
  
  -- flatten-frm pd j =
  --   equiv (flatten-frm-to pd j) (flatten-frm-from pd j)
  --         (flatten-frm-to-from pd j) (flatten-frm-from-to pd j)

  substitute (lf i) κ = lf i
  substitute (nd (f , ϕ)) κ =
    let pd = κ (_ , f) (inl idp)
        κ' j p g n = κ g (inr (j , p , n))
        θ j p = substitute (ϕ j p) (κ' j p)
        ψ j = flatten-leaf-elim pd j (cst (W P j)) (θ j)
    in graft P (flatten pd) ψ

  substitute-leaf-in (lf i) κ j l = l
  substitute-leaf-in (nd (f , ϕ)) κ j (h , p , l) =
    let pd = κ (_ , f) (inl idp)
        κ' j p g n = κ g (inr (j , p , n))
        θ j p = substitute (ϕ j p) (κ' j p)
        ψ j = flatten-leaf-elim pd j (cst (W P j)) (θ j)
    in graft-leaf-in P (flatten pd) ψ j h (flatten-leaf-in pd h p)
         (transport! (λ x → Leaf P x j) (flatten-leaf-elim-β pd h (cst (W P h)) (θ h) p) 
           (substitute-leaf-in (ϕ h p) (κ' h p) j l))


  -- substitute-leaf-elim : ∀ {ℓ'} {i : I} (w : W P i)
  --   → (κ : (g : Ops P) → Node P w g → W (P // R) g) (j : I)
  --   → (Q : Leaf P (substitute w κ) j → Type ℓ')
  --   → (σ : (l : Leaf P w j) → Q (substitute-leaf-in w κ j l))
  --   → (l : Leaf P (substitute w κ) j) → Q l

  substitute-leaf-elim (lf i) κ .i Q σ idp = σ idp
  substitute-leaf-elim (nd (f , ϕ)) κ j Q σ l = 
    let pd = κ (_ , f) (inl idp)
        κ' j p g n = κ g (inr (j , p , n))
        θ j p = substitute (ϕ j p) (κ' j p)
        ψ j = flatten-leaf-elim pd j (cst (W P j)) (θ j)
        -- Okay, I see.  *First* split l into its components
        -- This does not depend on any parameters.
        (h , l₀ , l₁) = graft-leaf-from P (flatten pd) ψ j l
        p₀ = flatten-leaf-elim pd h (cst (Param P f h)) (idf _) l₀

        -- Okay, so this, then is the η rule for flatten-leaf-elim.
        test₀ : flatten-leaf-in pd h p₀ == l₀
        test₀ = {!!}

        test : flatten-leaf-elim pd h (cst (W P h)) (θ h) l₀ == substitute (ϕ h p₀) (κ' h p₀)
        test = ap (flatten-leaf-elim pd h (cst (W P h)) (θ h)) (! test₀) ∙
                  flatten-leaf-elim-β pd h (cst (W P h)) (θ h) p₀ 

        l₁' : Leaf P (substitute (ϕ h p₀) (κ' h p₀)) j
        l₁' = transport (λ x → Leaf P x j) test l₁
        
    in transport Q {!!} (substitute-leaf-elim (ϕ h p₀) (κ' h p₀) j (λ x → Q (graft-leaf-in P (flatten pd) ψ j h l₀ (transport! (λ y → Leaf P y j) test x))) {!!} l₁') 

  -- substitute-lf-to (lf i) κ j l = l
  -- substitute-lf-to (nd {i} (f , ϕ)) κ j l = 
  --   let pd = κ (i , f) (inl idp)
  --       p j l = flatten-frm-to pd j l
  --       κ' j l ic n = κ ic (inr (j , p j l , n))
  --       ε j l = substitute (ϕ j (p j l)) (λ ic n → κ ic (inr (j , p j l , n)))
  --       (k , l₀ , l₁) = graft-leaf-to P (flatten pd) ε j l
  --       p' = flatten-frm-to pd k l₀
  --       l' = substitute-lf-to (ϕ k (p k l₀)) (κ' k l₀) j l₁
  --   in (k , p' , l')

  -- substitute-leaf-elim-β : ∀ {ℓ'} {i : I} (w : W P i)
  --   → (κ : (g : Ops P) → Node P w g → W (P // R) g) (j : I)
  --   → (Q : Leaf P (substitute w κ) j → Type ℓ')
  --   → (σ : (l : Leaf P w j) → Q (substitute-leaf-in w κ j l))
  --   → (l : Leaf P w j)
  --   → substitute-leaf-elim w κ j Q σ (substitute-leaf-in w κ j l) == σ l
  
  substitute-leaf-elim-β = {!!}

  -- substitute-lf-from (lf i) κ j l = l
  -- substitute-lf-from (nd {i} (f , ϕ)) κ j (k , p' , ll) = 
  --   let pd = κ (i , f) (inl idp)
  --       p j l = flatten-frm-to pd j l
  --       κ' j l ic n = κ ic (inr (j , p j l , n))
  --       ε j l = substitute (ϕ j (p j l)) (κ' j l)
  --       l' = flatten-frm-from pd k p'
  --       ll' = substitute-lf-from (ϕ k p') (λ ic n → κ ic (inr (k , p' , n))) j ll
  --       Q x = Leaf P (substitute (ϕ k x) (λ ic n → κ ic (inr (k , x , n)))) j
  --   in graft-leaf-from P (flatten pd) ε j (k , l' , transport! Q (flatten-frm-to-from pd k p') ll')

  -- substitute-lf-eqv w κ j =
  --   equiv (substitute-lf-to w κ j) (substitute-lf-from w κ j)
  --         (substitute-lf-to-from w κ j) (substitute-lf-from-to w κ j)

  -- --
  -- --  The Baez-Dolan Frame
  -- --
  
  -- bd-frame-to : {i : I} {f : Op P i}
  --   → (pd : W (P // R) (i , f)) (jg : Σ I (Op P))
  --   → Leaf (P // R) pd jg → Node P (flatten pd) (snd jg)

  -- bd-frame-from : {i : I} {f : Op P i}
  --   → (pd : W (P // R) (i , f)) (jg : Σ I (Op P))
  --   → Node P (flatten pd) (snd jg) → Leaf (P // R) pd jg

  -- postulate
  
  --   bd-frame-to-from : {i : I} {f : Op P i}
  --     → (pd : W (P // R) (i , f)) (jg : Σ I (Op P))
  --     → (n : Node P (flatten pd) (snd jg))
  --     → bd-frame-to pd jg (bd-frame-from pd jg n) == n

  --   bd-frame-from-to : {i : I} {f : Op P i}
  --     → (pd : W (P // R) (i , f)) (jg : Σ I (Op P))
  --     → (l : Leaf (P // R) pd jg)
  --     → bd-frame-from pd jg (bd-frame-to pd jg l) == l

  -- bd-frame : {i : I} {f : Op P i}
  --   → (pd : W (P // R) (i , f))
  --   → (jg : Σ I (Op P)) → Leaf (P // R) pd jg ≃ Node P (flatten pd) (snd jg)

  -- --
  -- --  Nodes in a substituted tree
  -- --

  -- substitute-nd-to : {i : I} (w : W P i)
  --   → (κ : (c : Σ I (Op P)) → Node P w (snd c) → W (P // R) c) (jg : Σ I (Op P))
  --   → Σ (Σ I (Op P)) (λ ke → Σ (Node P w (snd ke)) (λ n → Leaf (P // R) (κ ke n) jg))
  --   → Node P (substitute w κ) (snd jg) 

  -- substitute-nd-from : {i : I} (w : W P i)
  --   → (κ : (c : Σ I (Op P)) → Node P w (snd c) → W (P // R) c) (jg : Σ I (Op P))
  --   → Node P (substitute w κ) (snd jg) 
  --   → Σ (Σ I (Op P)) (λ ke → Σ (Node P w (snd ke)) (λ n → Leaf (P // R) (κ ke n) jg))

  -- postulate
  
  --   substitute-nd-to-from : {i : I} (w : W P i)
  --     → (κ : (c : Σ I (Op P)) → Node P w (snd c) → W (P // R) c) (jg : Σ I (Op P))
  --     → (n : Node P (substitute w κ) (snd jg))
  --     → substitute-nd-to w κ jg (substitute-nd-from w κ jg n) == n

  --   substitute-nd-from-to : {i : I} (w : W P i)
  --     → (κ : (c : Σ I (Op P)) → Node P w (snd c) → W (P // R) c) (jg : Σ I (Op P))
  --     → (t : Σ (Σ I (Op P)) (λ ke → Σ (Node P w (snd ke)) (λ n → Leaf (P // R) (κ ke n) jg)))
  --     → substitute-nd-from w κ jg (substitute-nd-to w κ jg t) == t

  -- substitute-nd-eqv : {i : I} (w : W P i)
  --   → (κ : (c : Σ I (Op P)) → Node P w (snd c) → W (P // R) c)
  --   → (jg : Σ I (Op P))
  --   → Σ (Σ I (Op P)) (λ ke → Σ (Node P w (snd ke)) (λ n → Leaf (P // R) (κ ke n) jg))
  --   ≃ Node P (substitute w κ) (snd jg) 

  -- --
  -- --  Implementation
  -- --

  -- bd-frame-to (lf .(j , g)) (j , g) idp = (inl idp)
  -- bd-frame-to (nd ((w , α , r) , κ)) = substitute-nd-to w κ
  
  -- bd-frame-from (lf .(j , g)) (j , g) (inl idp) = idp
  -- bd-frame-from (lf .(_ , _)) (j , g) (inr (_ , p , ()))
  -- bd-frame-from (nd ((w , α , r) , κ)) = substitute-nd-from w κ 
    
  -- bd-frame pd jg =
  --   equiv (bd-frame-to pd jg) (bd-frame-from pd jg)
  --         (bd-frame-to-from pd jg) (bd-frame-from-to pd jg)

  -- substitute-nd-to (lf i) κ (j , g) ((k , e) , () , l)
  -- substitute-nd-to (nd (f , ϕ)) κ (j , g) ((k , .f) , (inl idp) , l) = 
  --   let pd = κ (k , f) (inl idp) 
  --       p j l = flatten-frm-to pd j l
  --       κ' j l ic n = κ ic (inr (j , p j l , n))
  --       ε j l = substitute (ϕ j (p j l)) (κ' j l) 
  --   in graft-node-to P (flatten pd) ε g (inl (bd-frame-to pd (j , g) l))
    
  -- substitute-nd-to (nd {i} (f , ϕ)) κ (j , g) ((k , e) , (inr (a , p' , n)) , l) = 
  --   let pd = κ (i , f) (inl idp) 
  --       p j l = flatten-frm-to pd j l
  --       κ' j l ic n = κ ic (inr (j , p j l , n))
  --       ε j l = substitute (ϕ j (p j l)) (κ' j l)
  --       l' = flatten-frm-from pd a p'
  --       Q x = Node P (substitute (ϕ a x) (λ ic n → κ ic (inr (a , x , n)))) g
  --       n' = substitute-nd-to (ϕ a p') (λ ic n₀ → κ ic (inr (a , p' , n₀))) (j , g) ((k , e) , n , l)
  --   in graft-node-to P (flatten pd) ε g (inr (a , l' , transport! Q (flatten-frm-to-from pd a p') n' ))
    
  -- substitute-nd-from (lf i) κ (j , g) ()
  -- substitute-nd-from (nd {i} (f , ϕ)) κ (j , g) n with graft-node-from P (flatten (κ (i , f) (inl idp))) _ g n
  -- substitute-nd-from (nd {i} (f , ϕ)) κ (j , g) n | inl n' =
  --   (i , f) , (inl idp) , (bd-frame-from (κ (i , f) (inl idp)) (j , g) n')
  -- substitute-nd-from (nd {i} (f , ϕ)) κ (j , g) n | inr (k , l' , n') = 
  --   let pd = κ (i , f) (inl idp) 
  --       p j l = flatten-frm-to pd j l
  --       κ' j l ic n = κ ic (inr (j , p j l , n))
  --       ε j l = substitute (ϕ j (p j l)) (κ' j l)
  --       p' = flatten-frm-to pd k l'
  --       (ke , n'' , l'') = substitute-nd-from (ϕ k p') (λ ic n₀ → κ ic (inr (k , p' , n₀))) (j , g) n'
  --   in ke , (inr (k , p' , n'')) , l''
    
  -- substitute-nd-eqv w κ jg =
  --   equiv (substitute-nd-to w κ jg) (substitute-nd-from w κ jg)
  --         (substitute-nd-to-from w κ jg) (substitute-nd-from-to w κ jg)





