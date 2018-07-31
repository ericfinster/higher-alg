{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial

module Morphism where

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
      → (w : W (ΣPoly Q) (i , m))
      → {j : I} {n : ι-ext Q j}
      → Leaf (ΣPoly Q) w (j , n)
      → Leaf P (W-map w) j
    W-map-lf-to (lf (i , m)) (leaf .(i , m)) = leaf i
    W-map-lf-to (nd ((c , d) , δ)) {j} {n} (stem {j = k , o} (p , q) l) =
      stem p (W-map-lf-to (δ (_ , ρ-ext-typ Q d p) (p , ρ-ext-val Q d p)) {j} {n} (transport L coh l))

      where L : Σ (ι-ext Q k) (ρ-ext Q d p) → Type₀
            L (a , b) = Leaf (ΣPoly Q) (δ (k , a) (p , b)) (j , n)
  
            coh : (o , q) == (ρ-ext-typ Q d p , ρ-ext-val Q d p)
            coh = ! (contr-path (ρ-ext-contr Q d p) (o , q))

    W-map-lf-from : {i : I} {m : ι-ext Q i}
      → (w : W (ΣPoly Q) (i , m))
      → {j : I} 
      → Leaf P (W-map w) j
      → Σ (ι-ext Q j) (λ n → Leaf (ΣPoly Q) w (j , n))
    W-map-lf-from (lf (i , m)) {.i} (leaf .i) = m , leaf (i , m)
    W-map-lf-from (nd ((c , d) , δ)) {j} (stem p l) with W-map-lf-from (δ (_ , ρ-ext-typ Q d p) (p , ρ-ext-val Q d p)) l
    W-map-lf-from (nd ((c , d) , δ)) {j} (stem {j = k} p l) | (n , l') = n , stem (p , ρ-ext-val Q d p) l'


  -- This alternate, functional style version may be useful at some
  -- point as well, but for now, I will stick with the fibrational
  -- picture ...
  
  -- record PolyMorph {I J : Type₀} (P : Poly I) (Q : Poly J) : Type₀ where
  --   field
  --     α : I → J
  --     β : {i : I} → γ P i → γ Q (α i)
  --     θ : {i : I} (c : γ P i) {j : J}
  --       →  ρ Q (β c) j ≃ Σ (hfiber α j) (λ x → ρ P c (fst x))
