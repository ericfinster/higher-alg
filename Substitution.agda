{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial

module Substitution {ℓ} {I : Type ℓ} (P : Poly I) where

  -- The substitution polynomial
  Subst : Poly (Ops P)
  Op Subst (i , f) = Σ (W P i) (λ w → Frame P w f)
  Param Subst (w , _) = Node P w

  -- Elementary substitution.
  subst : {i : I} (w : W P i)
    → (κ : (g : Ops P) → Node P w g → Op Subst g)
    → W P i
  subst (lf i) κ = lf i
  subst (nd (f , ϕ)) κ =
    let (w , α) = κ (_ , f) (inl idp)
        κ' j l g n = κ g (inr (j , –> (α j) l , n))
        ψ j l = subst (ϕ j (–> (α j) l)) (κ' j l)
    in graft P w ψ

  -- Leaves in a substitution
  subst-lf-to : {i : I} (w : W P i)
    → (κ : (g : Ops P) → Node P w g → Op Subst g)
    → (j : I) → Leaf P (subst w κ) j → Leaf P w j
  subst-lf-to (lf i) κ j l = l
  subst-lf-to (nd (f , ϕ)) κ j l = 
    let (w , α) = κ (_ , f) (inl idp)
        κ' j l g n = κ g (inr (j , –> (α j) l , n))
        ψ j l = subst (ϕ j (–> (α j) l)) (κ' j l)
        (k , l₀ , l₁) = graft-leaf-from P w ψ j l
    in k , –> (α k) l₀ , subst-lf-to (ϕ k (–> (α k) l₀)) (κ' k l₀) j l₁ 
    
  subst-lf-from : {i : I} (w : W P i)
    → (κ : (g : Ops P) → Node P w g → Op Subst g)
    → (j : I) → Leaf P w j → Leaf P (subst w κ) j 
  subst-lf-from (lf i) κ j l = l
  subst-lf-from (nd (f , ϕ)) κ j (k , p , l) = 
    let (w , α) = κ (_ , f) (inl idp)
        κ' j l g n = κ g (inr (j , –> (α j) l , n))
        ψ j l = subst (ϕ j (–> (α j) l)) (κ' j l)
        l' = subst-lf-from (ϕ k p) (λ g n → κ g (inr (k , p , n))) j l
        Q x = Leaf P (subst (ϕ k x) (λ g n → κ g (inr (k , x , n)))) j
    in graft-leaf-to P w ψ j (k , <– (α k) p , transport! Q (<–-inv-r (α k) p) l')

  postulate

    subst-lf-to-from : {i : I} (w : W P i)
      → (κ : (g : Ops P) → Node P w g → Op Subst g)
      → (j : I) (l : Leaf P w j)
      → subst-lf-to w κ j (subst-lf-from w κ j l) == l
      
    subst-lf-from-to : {i : I} (w : W P i)
      → (κ : (g : Ops P) → Node P w g → Op Subst g)
      → (j : I) (l : Leaf P (subst w κ) j)
      → subst-lf-from w κ j (subst-lf-to w κ j l) == l

  subst-lf-eqv : {i : I} (w : W P i)
    → (κ : (g : Ops P) → Node P w g → Op Subst g)
    → (j : I) → Leaf P (subst w κ) j ≃ Leaf P w j
  subst-lf-eqv w κ j = equiv (subst-lf-to w κ j) (subst-lf-from w κ j)
    (subst-lf-to-from w κ j) (subst-lf-from-to w κ j)

  -- Iterated substitution
  μ-subst : {f : Ops P} → W Subst f → Op Subst f
  μ-subst {i , f} (lf .(i , f)) = corolla P f , corolla-lf-eqv P f
  μ-subst {i , f} (nd ((w , α) , κ)) =
    let κ' g n = μ-subst (κ g n)
    in subst w κ' , (λ j → α j ∘e (subst-lf-eqv w κ' j))

  postulate

    μ-subst-frm : {f : Ops P} (pd : W Subst f)
      → Frame Subst pd (μ-subst pd)

  -- Very nice.  So yes, this is considerably simpler, and even
  -- passes termination!  Excellent.

  -- And now, you can even see directly the next step:

  BD : Poly (Ops Subst)
  Op BD ((i , f) , (w , α)) = hfiber μ-subst (w , α)
  Param BD (pd , e) = Node Subst pd

  -- And from here, the pattern continues.
  -- So, what you have to show is that this "submonad" *also* admits
  -- a multiplication.  That is to say, that given a tree of
  -- pasting diagrams, each compatible with substitution, then we
  -- can glue them together to get a *new* pasting diagram which
  -- itself is compatible with substituion.

  -- record SubstPair {ℓ} {I : Type ℓ} (P : Poly I) (Q : Poly (Ops P)) : Type ℓ where
  --   field

  --     shell : {i : I} {f : Op P i} (u : Op Q (i , f)) → W P i
  --     shell-frm : {i : I} {f : Op P i} (u : Op Q (i , f)) → Frame P (shell u) f
  --     shell-nds : {i : I} {f : Op P i} (u : Op Q (i , f)) → (g : Ops P) → Node P (shell u) g ≃ Param Q u g

  -- module _ {ℓ} {I : Type ℓ} (P : Poly I) (Q : Poly (Ops P)) (Ψ : SubstPair P Q) where

  --   open SubstPair Ψ

  --   --
  --   --  Flattening, and the associated frame
  --   --

  --   flatten : {i : I} {f : Op P i} (pd : W Q (i , f)) → W P i

  --   flatten-frm-to : {i : I} {f : Op P i}
  --     → (pd : W Q (i , f))
  --     → (j : I) → Leaf P (flatten pd) j → Param P f j

  --   flatten-frm-from : {i : I} {f : Op P i}
  --     → (pd : W Q (i , f))
  --     → (j : I) → Param P f j → Leaf P (flatten pd) j 

  --   postulate

  --     flatten-frm-to-from : {i : I} {f : Op P i}
  --       → (pd : W Q (i , f))
  --       → (j : I) (p : Param P f j)
  --       → flatten-frm-to pd j (flatten-frm-from pd j p) == p

  --     flatten-frm-from-to : {i : I} {f : Op P i}
  --       → (pd : W Q (i , f))
  --       → (j : I) (l : Leaf P (flatten pd) j )
  --       → flatten-frm-from pd j (flatten-frm-to pd j l) == l

  --   -- The flattened tree has a canonical c-frame
  --   flatten-frm : {i : I} {f : Op P i}
  --     → (pd : W Q (i , f))
  --     → (j : I) → Leaf P (flatten pd) j ≃ Param P f j

  --   --
  --   --  Substituting, and the equivalence of leaves
  --   --

  --   substitute : {i : I} (w : W P i)
  --     → (κ : (g : Ops P) → Node P w g → W Q g)
  --     → W P i

  --   substitute-lf-to : {i : I} (w : W P i)
  --     → (κ : (g : Ops P) → Node P w g → W Q g)
  --     → (j : I) → Leaf P (substitute w κ) j → Leaf P w j

  --   substitute-lf-from : {i : I} (w : W P i)
  --     → (κ : (g : Ops P) → Node P w g → W Q g)
  --     → (j : I) → Leaf P w j → Leaf P (substitute w κ) j 

  --   postulate

  --     substitute-lf-to-from : {i : I} (w : W P i)
  --       → (κ : (g : Ops P) → Node P w g → W Q g)
  --       → (j : I) (l : Leaf P w j)
  --       → substitute-lf-to w κ j (substitute-lf-from w κ j l) == l

  --     substitute-lf-from-to : {i : I} (w : W P i)
  --       → (κ : (g : Ops P) → Node P w g → W Q g)
  --       → (j : I) (l : Leaf P (substitute w κ) j)
  --       → substitute-lf-from w κ j (substitute-lf-to w κ j l) == l

  --   -- A substituted tree has the same leaves
  --   substitute-lf-eqv : {i : I} (w : W P i)
  --     → (κ : (g : Ops P) → Node P w g → W Q g)
  --     → (j : I) → Leaf P (substitute w κ) j ≃ Leaf P w j

  --   --
  --   --  Implementation
  --   --

  --   flatten (lf (i , f)) = corolla P f
  --   flatten (nd (u , κ)) = substitute (shell u) (λ g → (κ g) ∘ (–> (shell-nds u g)))

  --   flatten-frm-to (lf _) j (_ , p , idp) = p
  --   flatten-frm-to (nd (u , κ)) j l =
  --     –> (shell-frm u j) (substitute-lf-to (shell u) (λ g → (κ g) ∘ (–> (shell-nds u g))) j l) 

  --   flatten-frm-from (lf (i , f)) j p = (j , p , idp)
  --   flatten-frm-from (nd (u , κ)) j p =
  --     substitute-lf-from (shell u) (λ g → (κ g) ∘ (–> (shell-nds u g))) j (<– (shell-frm u j) p)

  --   flatten-frm pd j =
  --     equiv (flatten-frm-to pd j) (flatten-frm-from pd j)
  --           (flatten-frm-to-from pd j) (flatten-frm-from-to pd j)

  --   substitute (lf i) κ = lf i
  --   substitute (nd {i} (f , ϕ)) κ = 
  --     let pd = κ (i , f) (inl idp)
  --         p j l = flatten-frm-to pd j l
  --         ε j l = substitute (ϕ j (p j l)) (λ ic n → κ ic (inr (j , p j l , n)))
  --     in graft P (flatten pd) ε 

  --   substitute-lf-to (lf i) κ j l = l
  --   substitute-lf-to (nd {i} (f , ϕ)) κ j l = 
  --     let pd = κ (i , f) (inl idp)
  --         p j l = flatten-frm-to pd j l
  --         κ' j l ic n = κ ic (inr (j , p j l , n))
  --         ε j l = substitute (ϕ j (p j l)) (λ ic n → κ ic (inr (j , p j l , n)))
  --         (k , l₀ , l₁) = graft-leaf-from P (flatten pd) ε j l
  --         p' = flatten-frm-to pd k l₀
  --         l' = substitute-lf-to (ϕ k (p k l₀)) (κ' k l₀) j l₁
  --     in (k , p' , l')

  --   substitute-lf-from (lf i) κ j l = l
  --   substitute-lf-from (nd {i} (f , ϕ)) κ j (k , p' , ll) = 
  --     let pd = κ (i , f) (inl idp)
  --         p j l = flatten-frm-to pd j l
  --         κ' j l ic n = κ ic (inr (j , p j l , n))
  --         ε j l = substitute (ϕ j (p j l)) (κ' j l)
  --         l' = flatten-frm-from pd k p'
  --         ll' = substitute-lf-from (ϕ k p') (λ ic n → κ ic (inr (k , p' , n))) j ll
  --         Q x = Leaf P (substitute (ϕ k x) (λ ic n → κ ic (inr (k , x , n)))) j
  --     in graft-leaf-to P (flatten pd) ε j (k , l' , transport! Q (flatten-frm-to-from pd k p') ll')

  --   substitute-lf-eqv w κ j =
  --     equiv (substitute-lf-to w κ j) (substitute-lf-from w κ j)
  --           (substitute-lf-to-from w κ j) (substitute-lf-from-to w κ j)

  --   --
  --   --  The Baez-Dolan Frame
  --   --

  --   bd-frame-to : {i : I} {f : Op P i}
  --     → (pd : W Q (i , f)) (jg : Ops P)
  --     → Leaf Q pd jg → Node P (flatten pd) jg

  --   bd-frame-from : {i : I} {f : Op P i}
  --     → (pd : W Q (i , f)) (jg : Ops P)
  --     → Node P (flatten pd) jg → Leaf Q pd jg

  --   postulate

  --     bd-frame-to-from : {i : I} {f : Op P i}
  --       → (pd : W Q (i , f)) (jg : Ops P)
  --       → (n : Node P (flatten pd) jg)
  --       → bd-frame-to pd jg (bd-frame-from pd jg n) == n

  --     bd-frame-from-to : {i : I} {f : Op P i}
  --       → (pd : W Q (i , f)) (jg : Ops P)
  --       → (l : Leaf Q pd jg)
  --       → bd-frame-from pd jg (bd-frame-to pd jg l) == l

  --   bd-frame : {i : I} {f : Op P i}
  --     → (pd : W Q (i , f))
  --     → (jg : Ops P) → Leaf Q pd jg ≃ Node P (flatten pd) jg

  --   --
  --   --  Nodes in a substituted tree
  --   --

  --   substitute-nd-to : {i : I} (w : W P i)
  --     → (κ : (g : Ops P) → Node P w g → W Q g) (jg : Ops P)
  --     → Σ (Ops P) (λ ke → Σ (Node P w ke) (λ n → Leaf Q (κ ke n) jg))
  --     → Node P (substitute w κ) jg 

  --   substitute-nd-from : {i : I} (w : W P i)
  --     → (κ : (g : Ops P) → Node P w g → W Q g) (jg : Ops P)
  --     → Node P (substitute w κ) jg 
  --     → Σ (Ops P) (λ ke → Σ (Node P w ke) (λ n → Leaf Q (κ ke n) jg))

  --   postulate

  --     substitute-nd-to-from : {i : I} (w : W P i)
  --       → (κ : (g : Ops P) → Node P w g → W Q g) (jg : Ops P)
  --       → (n : Node P (substitute w κ) jg)
  --       → substitute-nd-to w κ jg (substitute-nd-from w κ jg n) == n

  --     substitute-nd-from-to : {i : I} (w : W P i)
  --       → (κ : (g : Ops P) → Node P w g → W Q g) (jg : Ops P)
  --       → (t : Σ (Ops P) (λ ke → Σ (Node P w ke) (λ n → Leaf Q (κ ke n) jg)))
  --       → substitute-nd-from w κ jg (substitute-nd-to w κ jg t) == t

  --   substitute-nd-eqv : {i : I} (w : W P i)
  --     → (κ : (g : Ops P) → Node P w g → W Q g)
  --     → (jg : Ops P)
  --     → Σ (Ops P) (λ ke → Σ (Node P w ke) (λ n → Leaf Q (κ ke n) jg))
  --     ≃ Node P (substitute w κ) jg 

  --   --
  --   --  Implementation
  --   --

  --   bd-frame-to (lf .(j , g)) (j , g) idp = (inl idp)
  --   bd-frame-to (nd (u , κ)) = {! (substitute-nd-to (shell u) (λ g → (κ g) ∘ (–> (shell-nds u g)))) !}
  --     -- substitute-nd-to (shell u)
      

  --   bd-frame-from (lf .(j , g)) (j , g) (inl idp) = idp
  --   bd-frame-from (lf .(_ , _)) (j , g) (inr (_ , p , ()))
  --   bd-frame-from (nd (u , κ)) = {!!}
  --     -- substitute-nd-from (shell u)
  --     -- (λ g → (κ g) ∘ (–> (shell-nds u g)))

  --   bd-frame pd jg =
  --     equiv (bd-frame-to pd jg) (bd-frame-from pd jg)
  --           (bd-frame-to-from pd jg) (bd-frame-from-to pd jg)

  --   substitute-nd-to (lf i) κ (j , g) ((k , e) , () , l)
  --   substitute-nd-to (nd (f , ϕ)) κ (j , g) ((k , .f) , (inl idp) , l) = 
  --     let pd = κ (k , f) (inl idp) 
  --         p j l = flatten-frm-to pd j l
  --         κ' j l ic n = κ ic (inr (j , p j l , n))
  --         ε j l = substitute (ϕ j (p j l)) (κ' j l) 
  --     in graft-node-to P (flatten pd) ε (j , g) (inl (bd-frame-to pd (j , g) l))

  --   substitute-nd-to (nd {i} (f , ϕ)) κ (j , g) ((k , e) , (inr (a , p' , n)) , l) = 
  --     let pd = κ (i , f) (inl idp) 
  --         p j l = flatten-frm-to pd j l
  --         κ' j l ic n = κ ic (inr (j , p j l , n))
  --         ε j l = substitute (ϕ j (p j l)) (κ' j l)
  --         l' = flatten-frm-from pd a p'
  --         Q x = Node P (substitute (ϕ a x) (λ ic n → κ ic (inr (a , x , n)))) (j , g)
  --         n' = substitute-nd-to (ϕ a p') (λ ic n₀ → κ ic (inr (a , p' , n₀))) (j , g) ((k , e) , n , l)
  --     in graft-node-to P (flatten pd) ε (j , g) (inr (a , l' , transport! Q (flatten-frm-to-from pd a p') n' ))

  --   substitute-nd-from (lf i) κ (j , g) ()
  --   substitute-nd-from (nd {i} (f , ϕ)) κ (j , g) n with graft-node-from P (flatten (κ (i , f) (inl idp))) _ (j , g) n
  --   substitute-nd-from (nd {i} (f , ϕ)) κ (j , g) n | inl n' =
  --     (i , f) , (inl idp) , (bd-frame-from (κ (i , f) (inl idp)) (j , g) n')
  --   substitute-nd-from (nd {i} (f , ϕ)) κ (j , g) n | inr (k , l' , n') = 
  --     let pd = κ (i , f) (inl idp) 
  --         p j l = flatten-frm-to pd j l
  --         κ' j l ic n = κ ic (inr (j , p j l , n))
  --         ε j l = substitute (ϕ j (p j l)) (κ' j l)
  --         p' = flatten-frm-to pd k l'
  --         (ke , n'' , l'') = substitute-nd-from (ϕ k p') (λ ic n₀ → κ ic (inr (k , p' , n₀))) (j , g) n'
  --     in ke , (inr (k , p' , n'')) , l''

  --   substitute-nd-eqv w κ jg =
  --     equiv (substitute-nd-to w κ jg) (substitute-nd-from w κ jg)
  --           (substitute-nd-to-from w κ jg) (substitute-nd-from-to w κ jg)

  --   --
  --   --  Elimination Principles
  --   --

  --   flatten-lf-in : {i : I} {f : Op P i} (pd : W Q (i , f))
  --     → (j : I) → Param P f j → Leaf P (flatten pd) j 
  --   flatten-lf-in = flatten-frm-from 

  --   flatten-lf-elim : ∀ {ℓ'} {i : I} {f : Op P i}
  --     → (pd : W Q (i , f)) (j : I)
  --     → (Q : Leaf P (flatten pd) j → Type ℓ')
  --     → (σ : (p : Param P f j) → Q (flatten-lf-in pd j p))
  --     → (l : Leaf P (flatten pd) j) → Q l
  --   flatten-lf-elim pd j Q σ l = transport Q (<–-inv-l (flatten-frm pd j) l) (σ (flatten-frm-to pd j l))

  --   postulate

  --     flatten-lf-elim-β : ∀ {ℓ'} {i : I} {f : Op P i}
  --       → (pd : W Q (i , f)) (j : I)
  --       → (Q : Leaf P (flatten pd) j → Type ℓ')
  --       → (σ : (p : Param P f j) → Q (flatten-lf-in pd j p))
  --       → (p : Param P f j)
  --       → flatten-lf-elim pd j Q σ (flatten-lf-in pd j p) == σ p

  --   subst-lf-in : {i : I} (w : W P i)
  --     → (κ : (g : Ops P) → Node P w g → W Q g)
  --     → ∀ j → Leaf P w j → Leaf P (substitute w κ) j
  --   subst-lf-in = substitute-lf-from

  --   subst-lf-elim : ∀ {ℓ'} {i : I} (w : W P i)
  --     → (κ : (g : Ops P) → Node P w g → W Q g) (j : I)
  --     → (Q : Leaf P (substitute w κ) j → Type ℓ')
  --     → (σ : (l : Leaf P w j) → Q (subst-lf-in w κ j l))
  --     → (l : Leaf P (substitute w κ) j) → Q l
  --   subst-lf-elim w κ j Q σ l = transport Q (<–-inv-l (substitute-lf-eqv w κ j) l) (σ (substitute-lf-to w κ j l))

  --   postulate

  --     subst-lf-elim-β : ∀ {ℓ'} {i : I} (w : W P i)
  --       → (κ : (g : Ops P) → Node P w g → W Q g) (j : I)
  --       → (Q : Leaf P (substitute w κ) j → Type ℓ')
  --       → (σ : (l : Leaf P w j) → Q (subst-lf-in w κ j l))
  --       → (l : Leaf P w j)
  --       → subst-lf-elim w κ j Q σ (subst-lf-in w κ j l) == σ l


