{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import WPaths
open import Substitution
open import PolyMonad

module TreeLemmas where

  module _ {ℓ} {I : Type ℓ} (P : Poly I) where

    -- The height of a node
    height : {i : I} (w : W P i)
      → (g : Ops P) (n : Node P w g) → ℕ
    height (lf i) g (lift ())
    height (nd (f , ϕ)) .(_ , f) (inl idp) = 0
    height (nd (f , ϕ)) g (inr (k , p , n)) = S (height (ϕ k p) g n)

    -- We can extract a decoration given a node
    node-dec : {i : I} (w : W P i)
      → {j : I} (g : Op P j) 
      → Node P w (j , g)
      → Decor P g (W P)
    node-dec (lf i) g (lift ())
    node-dec (nd (f , ϕ)) .f (inl idp) = ϕ
    node-dec (nd (f , ϕ)) g (inr (k , p , n)) = node-dec (ϕ k p) g n

    -- We can extract a subtree
    subtree : {i : I} (w : W P i)
      → {j : I} (g : Op P j) 
      → Node P w (j , g)
      → W P j
    subtree (lf i) g (lift ())
    subtree (nd (f , ϕ)) .f (inl idp) = nd (f , ϕ)
    subtree (nd (f , ϕ)) g (inr (k , p , n)) = subtree (ϕ k p) g n

    -- This map should be monic, right?
    subtree-lf-to : {i : I} (w : W P i)
      → {j : I} (g : Op P j) (n : Node P w (j , g))
      → (k : I) (l : Leaf P (subtree w g n) k)
      → Leaf P w k
    subtree-lf-to (lf i) g (lift ()) k l 
    subtree-lf-to (nd (f , ϕ)) .f (inl idp) k l = l
    subtree-lf-to (nd (f , ϕ)) g (inr (h , p , n)) k l =
      h , p , subtree-lf-to (ϕ h p) g n k l

    -- Ungrafting
    ungraft : {i : I} (w : W P i) (ε : (g : Ops P) (n : Node P w g) → Bool)
      → Σ (W P i) (λ v → Decor (Fr P) v (W P))
    ungraft (lf i) ε = lf i , λ { i idp → lf i }
    ungraft (nd (f , ϕ)) ε with ε (_ , f) (inl idp)
    ungraft (nd (f , ϕ)) ε | true = nd (f , ϕ') , ψ

      where ih : (j : I) (p : Param P f j) → Σ (W P j) (λ v → Decor (Fr P) v (W P))
            ih j p = ungraft (ϕ j p) ε'

              where ε' : (g : Ops P) → Node P (ϕ j p) g → Bool
                    ε' g n = ε g (inr (j , p , n))

            ϕ' : (j : I) (p : Param P f j) → W P j
            ϕ' j p = fst (ih j p)

            ψ : (k : I) → Leaf P (nd (f , ϕ')) k → W P k
            ψ k (j , p , l) = snd (ih j p) k l

            
    ungraft {i} (nd (f , ϕ)) ε | false = lf i , λ { i idp → nd (f , ϕ) }
