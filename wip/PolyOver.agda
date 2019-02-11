{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Grafting
open import PolyMonad
open import wip.PolyEquiv
open import wip.PolyPaths

module wip.PolyOver where

  record PolyOver {ℓ} {I : Type ℓ} (P : Poly I) : Type (lsucc ℓ) where
    field
    
      Sort↓ : I → Type ℓ
      Op↓ : {i : I} (f : Op P i) (j : Sort↓ i) → Type ℓ
      Param↓ : {i : I} (f : Op P i) {j : Sort↓ i} (g : Op↓ f j)
        → {k : I} (p : Param P f k) → Sort↓ k 

  open PolyOver public

  ΣPoly : ∀ {ℓ} {I : Type ℓ} (P : Poly I) (Q : PolyOver P) → Poly (Σ I (Sort↓ Q))
  Op (ΣPoly P Q) (i , j) = Σ (Op P i) (λ f → Op↓ Q f j) 
  Param (ΣPoly P Q) (f , g) (k , l) = Σ (Param P f k) (λ p → Param↓ Q f g p == l)

  module _ {ℓ} {I : Type ℓ} {P : Poly I} (Q : PolyOver P) where

    -- Parameters are equivalent
    Param↓-eqv : {i : I} (f : Op P i) {j : Sort↓ Q i} (g : Op↓ Q f j)
      → (k : I) → Param P f k ≃ Σ (Sort↓ Q k) (λ h → Param (ΣPoly P Q) (f , g) (k , h))
    Param↓-eqv f g k = equiv (λ p → Param↓ Q f g p , p , idp)
                             (λ { (._ ,  p , idp) → p })
                             (λ { (._ , p , idp) → idp })
                             (λ p → idp)

    -- The induced map on trees from a morphism of polynomials.
    W↓ : {i : I} {j : Sort↓ Q i} → W (ΣPoly P Q) (i , j) → W P i
    W↓ (lf (i , j)) = lf i
    W↓ (nd {i , j} ((f , g) , ϕ)) =
      nd (f , λ k p → W↓ (ϕ (k , Param↓ Q f g p) (p , idp)))

    -- Leaves in a projected tree
    W↓-lf-to : {i : I} {j : Sort↓ Q i} (w : W (ΣPoly P Q) (i , j)) (k : I)
      → Σ (Sort↓ Q k) (λ m → Leaf (ΣPoly P Q) w (k , m))
      → Leaf P (W↓ w) k 
    W↓-lf-to (lf (i , j)) i (j , idp) = idp
    W↓-lf-to (nd ((f , g) , ϕ)) k (m , ((n , ._) , (p , idp) , l)) =
      n , p , W↓-lf-to (ϕ (n , Param↓ Q f g p) (p , idp)) k (m , l)

    W↓-lf-from : {i : I} {j : Sort↓ Q i} (w : W (ΣPoly P Q) (i , j)) (k : I)
      → Leaf P (W↓ w) k
      → Σ (Sort↓ Q k) (λ l → Leaf (ΣPoly P Q) w (k , l))
    W↓-lf-from (lf (i , j)) .i idp = j , idp
    W↓-lf-from (nd ((f , g) , ϕ)) k (m , p , l) = 
      let (n , l') = W↓-lf-from (ϕ (m , Param↓ Q f g p) (p , idp)) k l
      in n , (m , Param↓ Q f g p) , (p , idp) , l'

    W↓-lf-to-from : {i : I} {j : Sort↓ Q i} (w : W (ΣPoly P Q) (i , j)) (k : I)
      → (l : Leaf P (W↓ w) k)
      → W↓-lf-to w k (W↓-lf-from w k l) == l
    W↓-lf-to-from (lf (i , j)) .i idp = idp
    W↓-lf-to-from (nd ((f , g) , ϕ)) k (m , p , l) =
      ap (λ x → (m , p , x)) (W↓-lf-to-from (ϕ (m , Param↓ Q f g p) (p , idp)) k l)

    W↓-lf-from-to : {i : I} {j : Sort↓ Q i} (w : W (ΣPoly P Q) (i , j)) (k : I)
      → (l : Σ (Sort↓ Q k) (λ m → Leaf (ΣPoly P Q) w (k , m)))
      → W↓-lf-from w k (W↓-lf-to w k l) == l
    W↓-lf-from-to (lf .(i , j)) i (j , idp) = idp
    W↓-lf-from-to (nd ((f , g) , ϕ)) k (m , ((n , ._) , (p , idp) , l)) =
      ap (λ x → (fst x , (n , Param↓ Q f g p) , (p , idp) , snd x))
        (W↓-lf-from-to (ϕ (n , Param↓ Q f g p) (p , idp)) k (m , l))

    W↓-lf-eqv : {i : I} {j : Sort↓ Q i} (w : W (ΣPoly P Q) (i , j)) (k : I)
      → Σ (Sort↓ Q k) (λ l → Leaf (ΣPoly P Q) w (k , l)) ≃ Leaf P (W↓ w) k
    W↓-lf-eqv w k = equiv (W↓-lf-to w k) (W↓-lf-from w k)
                          (W↓-lf-to-from w k) (W↓-lf-from-to w k)

    -- Nodes in a projected tree
    W↓-nd-to : {i : I} {j : Sort↓ Q i} (w : W (ΣPoly P Q) (i , j)) (k : I) (h : Op P k)
      → Σ (Σ (Sort↓ Q k) (Op↓ Q h)) (λ { (m , o) → Node (ΣPoly P Q) w ((k , m) , (h , o)) })
      → Node P (W↓ w) (k , h)
    W↓-nd-to (lf .(_ , _)) k h ((m , g) , lift ())
    W↓-nd-to (nd ((f , g) , ϕ)) k .f ((m , .g) , inl idp) = inl idp
    W↓-nd-to (nd ((f , g) , ϕ)) k h ((m , l) , inr ((k₀ , ._) , (p , idp) , n)) =
      inr (k₀ , p , W↓-nd-to (ϕ (k₀ , Param↓ Q f g p) (p , idp)) k h ((m , l) , n))

    W↓-nd-from : {i : I} {j : Sort↓ Q i} (w : W (ΣPoly P Q) (i , j)) (k : I) (h : Op P k)
      → Node P (W↓ w) (k , h)
      → Σ (Σ (Sort↓ Q k) (Op↓ Q h)) (λ { (m , o) → Node (ΣPoly P Q) w ((k , m) , (h , o)) })
    W↓-nd-from (lf .(_ , _)) k h (lift ())
    W↓-nd-from (nd ((f , g) , ϕ)) k .f (inl idp) = (_ , g) , inl idp
    W↓-nd-from (nd ((f , g) , ϕ)) k h (inr (k₀ , p , n)) =
      let ((m , t) , n') = W↓-nd-from (ϕ (k₀ , Param↓ Q f g p) (p , idp)) k h n
      in (m , t) , inr ((k₀ , Param↓ Q f g p) , (p , idp) , n')

    W↓-nd-to-from : {i : I} {j : Sort↓ Q i} (w : W (ΣPoly P Q) (i , j)) (k : I) (h : Op P k)
      → (n : Node P (W↓ w) (k , h))
      → W↓-nd-to w k h (W↓-nd-from w k h n) == n
    W↓-nd-to-from (lf .(_ , _)) k h (lift ())
    W↓-nd-to-from (nd ((f , g) , ϕ)) k .f (inl idp) =  idp
    W↓-nd-to-from (nd ((f , g) , ϕ)) k h (inr (k₀ , p , n)) =
      ap (λ x → inr (k₀ , p , x)) (W↓-nd-to-from (ϕ (k₀ , Param↓ Q f g p) (p , idp)) k h n)

    W↓-nd-from-to : {i : I} {j : Sort↓ Q i} (w : W (ΣPoly P Q) (i , j)) (k : I) (h : Op P k)
      → (n : Σ (Σ (Sort↓ Q k) (Op↓ Q h)) (λ { (m , o) → Node (ΣPoly P Q) w ((k , m) , (h , o)) }))
      → W↓-nd-from w k h (W↓-nd-to w k h n) == n
    W↓-nd-from-to (lf .(_ , _)) k h ((m , g) , lift ())
    W↓-nd-from-to (nd ((f , g) , ϕ)) k .f ((m , .g) , inl idp) = idp
    W↓-nd-from-to (nd ((f , g) , ϕ)) k h ((m , l) , inr ((k₀ , ._) , (p , idp) , n)) =
      ap (λ x → fst x , inr ((k₀ , Param↓ Q f g p) , (p , idp) , snd x)) 
         (W↓-nd-from-to (ϕ (k₀ , Param↓ Q f g p) (p , idp)) k h ((m , l) , n))

    W↓-nd-eqv : {i : I} {j : Sort↓ Q i} (w : W (ΣPoly P Q) (i , j)) (k : I) (h : Op P k)
      → Σ (Σ (Sort↓ Q k) (Op↓ Q h)) (λ { (m , o) → Node (ΣPoly P Q) w ((k , m) , (h , o)) })
      ≃ Node P (W↓ w) (k , h)
    W↓-nd-eqv w k h = equiv (W↓-nd-to w k h) (W↓-nd-from w k h)
                            (W↓-nd-to-from w k h) (W↓-nd-from-to w k h)

    -- Projection of frames
    module _ {i : I} {f : Op P i} {j : Sort↓ Q i} {g : Op↓ Q f j}
      {w : W (ΣPoly P Q) (i , j)} (α : Frame (ΣPoly P Q) w (f , g)) (k : I) where
      
      Frame↓-to : Leaf P (W↓ w) k → Param P f k
      Frame↓-to l = let (h , l') = W↓-lf-from w k l
                    in fst (–> (α (k , h)) l')

      Frame↓-from : Param P f k → Leaf P (W↓ w) k 
      Frame↓-from p = W↓-lf-to w k (Param↓ Q f g p , <– (α (k , Param↓ Q f g p)) (p , idp))

      Frame↓-to-from : (p : Param P f k) → Frame↓-to (Frame↓-from p) == p
      Frame↓-to-from p = let (h , l') = W↓-lf-from w k (Frame↓-from p)
                         in fst (–> (α (k , h)) l')
                              =⟨ <–-inv-l (W↓-lf-eqv w k) (Param↓ Q f g p , <– (α (k , Param↓ Q f g p)) (p , idp))
                                   |in-ctx (λ x → fst (–> (α (k , fst x)) (snd x))) ⟩ 
                            fst (–> (α (k , Param↓ Q f g p)) (<– (α (k , Param↓ Q f g p)) (p , idp)))
                              =⟨ ap fst (<–-inv-r (α (k , Param↓ Q f g p)) (p , idp)) ⟩ 
                            p ∎

      Frame↓-from-lem : (p : Param P f k) (h : Sort↓ Q k) (e : Param↓ Q f g p == h)
        → W↓-lf-to w k (Param↓ Q f g p , <– (α (k , Param↓ Q f g p)) (p , idp))
          == W↓-lf-to w k (h , <– (α (k , h)) (p , e))
      Frame↓-from-lem p ._ idp = idp

      Frame↓-from-to : (l : Leaf P (W↓ w) k) → Frame↓-from (Frame↓-to l) == l
      Frame↓-from-to l = let (h , l') = W↓-lf-from w k l
                             (p , e) = –> (α (k , h)) l'
                         in W↓-lf-to w k (Param↓ Q f g p , <– (α (k , Param↓ Q f g p)) (p , idp))
                              =⟨ Frame↓-from-lem p h e ⟩ 
                            W↓-lf-to w k (h , <– (α (k , h)) (p , e))
                              =⟨ <–-inv-l (α (k , h)) l' |in-ctx (λ x → W↓-lf-to w k (h , x)) ⟩ 
                            W↓-lf-to w k (W↓-lf-from w k l)
                              =⟨ <–-inv-r (W↓-lf-eqv w k) l ⟩ 
                            l ∎


    Frame↓ : {i : I} {f : Op P i} {j : Sort↓ Q i} {g : Op↓ Q f j}
      → {w : W (ΣPoly P Q) (i , j)} (α : Frame (ΣPoly P Q) w (f , g))
      → Frame P (W↓ w) f
    Frame↓ α k = equiv (Frame↓-to α k) (Frame↓-from α k)
      (Frame↓-to-from α k) (Frame↓-from-to α k)
       
    -- Next, we show that projection commutes with grafting, substitution and flattening.
    graft↓ : {i : I} {j : Sort↓ Q i} (w : W (ΣPoly P Q) (i , j))
      → (ψ : (k : Σ I (Sort↓ Q)) → Leaf (ΣPoly P Q) w k → W (ΣPoly P Q) k)
      → W↓ (graft (ΣPoly P Q) w ψ) ==
        graft P (W↓ w) (λ j l → W↓ (ψ (j , fst (W↓-lf-from w j l)) (snd (W↓-lf-from w j l))))
    graft↓ (lf .(_ , _)) ψ = idp
    graft↓ (nd ((f , g) , ϕ)) ψ =
      let ψ' j p k l = ψ k ((j , Param↓ Q f g p) , (p , idp) , l)
      in ap (λ x → nd (f , x))
            (Decor-== P (λ j p → graft↓ (ϕ (j , Param↓ Q f g p ) (p , idp)) (ψ' j p)))

