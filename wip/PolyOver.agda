{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial

module PolyOver where

  record PolyOver {I : Type₀} (P : Poly I) : Type₁ where
    field
    
      ι-ext : I → Type₀
      γ-ext : {i : I} (m : ι-ext i) (c : γ P i) → Type₀
      ρ-ext : {i : I} {m : ι-ext i} {c : γ P i} (d : γ-ext m c)
        → {j : I} (p : ρ P c j) (n : ι-ext j) → Type₀

      ρ-ext-contr :  {i : I} {m : ι-ext i} {c : γ P i} (d : γ-ext m c)
        → {j : I} (p : ρ P c j) → is-contr (Σ (ι-ext j) (ρ-ext d p))

    ρ-ext-typ : {i : I} {m : ι-ext i} {c : γ P i} (d : γ-ext m c)
      → {j : I} (p : ρ P c j) → ι-ext j
    ρ-ext-typ d p = fst (contr-center (ρ-ext-contr d p))

    ρ-ext-val : {i : I} {m : ι-ext i} {c : γ P i} (d : γ-ext m c)
      → {j : I} (p : ρ P c j) → ρ-ext d p (ρ-ext-typ d p)
    ρ-ext-val d p = snd (contr-center (ρ-ext-contr d p))

  open PolyOver public

  ΣPoly : {I : Type₀} {P : Poly I} (Q : PolyOver P) → Poly (Σ I (ι-ext Q))
  γ (ΣPoly {P = P} Q) (i , m) = Σ (γ P i) (γ-ext Q m)
  ρ (ΣPoly {P = P} Q) {i , m} (c , d) (j , n) = Σ (ρ P c j) (λ p → ρ-ext Q d p n)

  Σρ : {I : Type₀} {P : Poly I} (Q : PolyOver P)
    → {i : I} {m : ι-ext Q i} {cd : γ (ΣPoly Q) (i , m)}
    → {j : I} (p : ρ P (fst cd) j) → ρ (ΣPoly Q) cd (j , ρ-ext-typ Q (snd cd) p)
  Σρ Q {cd = c , d} p = p , ρ-ext-val Q d p

  module _ {I : Type₀} {P : Poly I} (Q : PolyOver P) where

    -- The induced map on trees from a morphism of polynomials.
    W-map : {i : I} {j : ι-ext Q i} → W (ΣPoly Q) (i , j) → W P i
    W-map (lf (i , j)) = lf i
    W-map (nd {i , j} ((c , d) , δ)) =
      nd (c , λ k p → W-map (δ (k , ρ-ext-typ Q d p) (p , ρ-ext-val Q d p)))

    W-map-lf-to : {i : I} {m : ι-ext Q i}
      → (w : W (ΣPoly Q) (i , m)) {j : I} 
      → Σ (ι-ext Q j) (λ n → Leaf (ΣPoly Q) w (j , n))
      → Leaf P (W-map w) j
    W-map-lf-to (lf (i , m)) (.m , leaf .(i , m)) = leaf i
    W-map-lf-to (nd ((c , d) , δ)) {j} (n , stem {j = k , o} (p , q) l) =
      stem p (W-map-lf-to (δ (_ , ρ-ext-typ Q d p) (p , ρ-ext-val Q d p)) {j} (n , transport L coh l))

      where L : Σ (ι-ext Q k) (ρ-ext Q d p) → Type₀
            L (a , b) = Leaf (ΣPoly Q) (δ (k , a) (p , b)) (j , n)
  
            coh : (o , q) == (ρ-ext-typ Q d p , ρ-ext-val Q d p)
            coh = ! (contr-path (ρ-ext-contr Q d p) (o , q))

    W-map-lf-from : {i : I} {m : ι-ext Q i}
      → (w : W (ΣPoly Q) (i , m)) {j : I} 
      → Leaf P (W-map w) j
      → Σ (ι-ext Q j) (λ n → Leaf (ΣPoly Q) w (j , n))
    W-map-lf-from (lf (i , m)) {.i} (leaf .i) = m , leaf (i , m)
    W-map-lf-from (nd ((c , d) , δ)) {j} (stem p l) with W-map-lf-from (δ (_ , ρ-ext-typ Q d p) (p , ρ-ext-val Q d p)) l
    W-map-lf-from (nd ((c , d) , δ)) {j} (stem {j = k} p l) | (n , l') = n , stem (p , ρ-ext-val Q d p) l'

    postulate

      -- These should be easy, if tedious ...
      W-map-lf-to-from : {i : I} {m : ι-ext Q i}
        → (w : W (ΣPoly Q) (i , m)) {j : I} 
        → (l : Leaf P (W-map w) j)
        → W-map-lf-to w (W-map-lf-from w l) == l

      W-map-lf-from-to : {i : I} {m : ι-ext Q i}
        → (w : W (ΣPoly Q) (i , m)) {j : I} 
        → (l : Σ (ι-ext Q j) (λ n → Leaf (ΣPoly Q) w (j , n)))
        → W-map-lf-from w (W-map-lf-to w l) == l

    W-map-lf-eqv : {i : I} {m : ι-ext Q i}
      → (w : W (ΣPoly Q) (i , m)) {j : I} 
      → Σ (ι-ext Q j) (λ n → Leaf (ΣPoly Q) w (j , n))
      ≃ Leaf P (W-map w) j
    W-map-lf-eqv w = equiv (W-map-lf-to w) (W-map-lf-from w)
                           (W-map-lf-to-from w) (W-map-lf-from-to w)

    -- Uh, yeah, the naming here should be improved ...
    module _ {i : I} {m : ι-ext Q i}
      (w : W (ΣPoly Q) (i , m)) (c : γ P i) (d : γ-ext Q m c)
      (f :  Frame (ΣPoly Q) w (c , d)) {k : I} where
      
      W-frame-lf-to : Leaf P (W-map w) k → ρ P c k
      W-frame-lf-to l = 
        let (p' , l') = W-map-lf-from w l
        in fst (–> (f (k , p')) l')

      W-frame-lf-from : ρ P c k → Leaf P (W-map w) k
      W-frame-lf-from p = W-map-lf-to w (ρ-ext-typ Q d p , <– (f (k , ρ-ext-typ Q d p)) (p , ρ-ext-val Q d p))

      postulate

        W-frame-lf-to-from : (p : ρ P c k)
          → W-frame-lf-to (W-frame-lf-from p) == p

        W-frame-lf-from-to : (l : Leaf P (W-map w) k)
          → W-frame-lf-from (W-frame-lf-to l) == l

      W-frame-lf-eqv : Leaf P (W-map w) k ≃ ρ P c k
      W-frame-lf-eqv = equiv W-frame-lf-to W-frame-lf-from
                             W-frame-lf-to-from W-frame-lf-from-to

    -- The induced action on frames
    W-map-frame-to : {i : I} {m : ι-ext Q i}
      → (w : W (ΣPoly Q) (i , m)) 
      → (cd : γ (ΣPoly Q) (i , m))
      → Frame (ΣPoly Q) w cd → Frame P (W-map w) (fst cd)
    W-map-frame-to w (c , d) f k = W-frame-lf-eqv w c d f {k} 
    
    -- Using the above forgetful maps, we can pull back filling families
    PbFam : FillingFamily P → FillingFamily (ΣPoly Q)
    PbFam F w (c , d) f = F (W-map w) c (W-map-frame-to w (c , d) f)

    -- We can also use them to define a polynomial over the filling polynomial
    ExtPoly : (F : FillingFamily P) → PolyOver (P // F)
    ι-ext (ExtPoly F) (i , c) = Σ (ι-ext Q i) (λ m → γ-ext Q m c)
    γ-ext (ExtPoly F) {i , c} (m , d) (w , f , x) =
      Σ (W (ΣPoly Q) (i , m)) (λ w' →
      Σ (Frame (ΣPoly Q) w' (c , d)) (λ f' →
      Σ (W-map w' == w) (λ pth →
      W-map-frame-to w' (c , d) f' == f [ (λ w₀ → Frame P w₀ c) ↓ pth ])))
    ρ-ext (ExtPoly F) (w' , _ , _ , _) {_ , c₀} n₀ (_ , e) = Σ (Node (ΣPoly Q) w' (c₀ , e)) (λ nn → {!!})
    ρ-ext-contr (ExtPoly F) = {!!}
