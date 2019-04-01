{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import UniCat
open import homotopy.FinSet

module wip.Delta where

  open UniCat.PreCategory
  open UniCat.Category

  module ThirdDef where

    is-ord-pres : ∀ {m n : ℕ} (f : Fin m → Fin n) → Type₀
    is-ord-pres {m} {n} f = {x y : Fin m} → (fst x) < (fst y) → fst (f x) < fst (f y)

    is-ord-pres-is-prop : ∀ {m n : ℕ} (f : Fin m → Fin n) → is-prop (is-ord-pres f)
    is-ord-pres-is-prop  _ = Πi-level λ _ → Πi-level λ _ → Π-level λ _ → <-is-prop

    is-ord-pres-prop : (m n : ℕ) → SubtypeProp (Fin m → Fin n) lzero
    is-ord-pres-prop m n = is-ord-pres , is-ord-pres-is-prop

    -- Order preserving map (OPM for short)
    ord-pres-map : (m n : ℕ) → Type₀
    ord-pres-map m n = Subtype (is-ord-pres-prop m n)

    ord-pres-map-is-set : (m n : ℕ) → is-set (ord-pres-map m n)
    ord-pres-map-is-set m n = Subtype-level (is-ord-pres-prop m n) ⦃ Π-level λ _ → Fin-is-set ⦄ 

    -- The following definitions are used to show that Delta is a univalent category
    module _ {m n : ℕ} (f : ord-pres-map (S m) (S n)) (fm=n : fst (fst f (m , ltS)) == n) where

      -- Restriction of an OPM, from S m to S n, to m provided f m = n
      restrict : Fin m → Fin n
      restrict x with ℕ-trichotomy (fst (fst f (Fin-S x))) n 
      ... | inl fx=n       = ⊥-rec ((<-to-≠ (snd f (snd x))) (fx=n ∙ (! fm=n)) )
      ... | inr (inl fx<n) = fst (fst f (fst x , ltSR (snd x))) , fx<n
      ... | inr (inr n<fx) =
        let fm<fx = transport (λ z → z < (fst (fst f (fst x , ltSR (snd x))))) (! fm=n) n<fx
        in ⊥-rec (<-neg-commut (snd f (snd x)) fm<fx)

      -- The restricted map agrees with the original map on their common domain
      restrict-law : (x : Fin m) → fst (restrict x) == fst (fst f (Fin-S x))
      restrict-law x with ℕ-trichotomy (fst (fst f (Fin-S x))) n
      ... | inl fx=n       = ⊥-rec (((<-to-≠ (snd f (snd x))) (fx=n ∙ (! fm=n)) ))
      ... | inr (inl fx<n) = idp
      ... | inr (inr n<fx) =
        let fm<fx = transport (λ z → z < (fst (fst f (fst x , ltSR (snd x))))) (! fm=n) n<fx
        in ⊥-rec (<-neg-commut (snd f (snd x)) fm<fx)

      opm-restrict :  ord-pres-map m n
      opm-restrict = (restrict , ord-pres)
        where ord-pres : is-ord-pres restrict
              ord-pres x<y =  transport (λ { (x , y) → x < y }) (pair×= (! (restrict-law _)) (! (restrict-law _))) (snd f x<y)
    
    opm-endo-lem : (m : ℕ) (f : ord-pres-map m m) → fst f == idf _
    opm-endo-lem m (f , p) = λ= pth
      where lem-fx<x : {m : ℕ} (f : ord-pres-map m m) (n : ℕ) (n<m : n < m) → ¬ (fst ((fst f) (n , n<m)) < n)
            lem-fx<x (f , p) O  _     q = ≮O _ q
            lem-fx<x (f , p) (S n) n<m q =
              let ffn<n = (<-trans ((p {f (n , <-trans ltS n<m)} {f (S n , n<m)}) (p ltS)) (<-trans-pred (p q) q))
              in lem-fx<x (f ∘ f ,  p ∘ p) n (<-trans ltS n<m) ffn<n

            lem-x<fx : {m : ℕ} (f : ord-pres-map m m) (n : ℕ) (n<m : n < m) → ¬ (n < fst ((fst f) (n , n<m)))
            lem-x<fx {S m} (f , p) .m ltS q = <-irrefl (<-trans-pred q  (snd (f (m , ltS))))
            lem-x<fx {S m} (f , p) n (ltSR n<m) n<fn = lem-x<fx (opm-restrict (f , p) fm=m) n n<m n<f|n
              where fm=m : fst (f (m , ltS)) == m
                    fm=m with ℕ-trichotomy (fst (f (m , ltS))) m
                    ... | inl fm=m = fm=m
                    ... | inr (inl fm<m) = ⊥-rec (lem-fx<x (f , p) m ltS fm<m) 
                    ... | inr (inr m<fm) = ⊥-rec (m<n<Sm m<fm (snd (f (m , ltS))))

                    f|n=fn = restrict-law (f , p) fm=m (n , n<m)

                    n<f|n  = transport (λ x → n < x) (! f|n=fn) n<fn

            pth : (x : Fin m) → f x == x
            pth x with ℕ-trichotomy (fst (f x)) (fst x)
            ... | inl fx=x       = Subtype=-out (Fin-prop m) fx=x
            ... | inr (inl fx<x) = ⊥-rec (lem-fx<x (f , p) (fst x) (snd x) fx<x) 
            ... | inr (inr x<fx) = ⊥-rec (lem-x<fx (f , p) (fst x) (snd x) x<fx)

    hom-is-contr : (m : ℕ) → is-contr (ord-pres-map m m)
    hom-is-contr m = has-level-in ((idf _ , idf _) , λ f → Subtype=-out (is-ord-pres-prop _ _) (! (opm-endo-lem m f)))

    PDelta : PreCategory lzero lzero
    obj           PDelta                 = ℕ 
    hom           PDelta m n             = ord-pres-map m n
    _●_           PDelta (g , q) (f , p) = g ∘ f  , q ∘ p   
    assoc         PDelta _ _ _           = idp
    id            PDelta                 = (idf _ , idf _)
    unit-l        PDelta _               = idp
    unit-r        PDelta _               = idp
    homs-sets     PDelta                 = ord-pres-map-is-set

    open PreCategory PDelta

    PDelta-is-univalent : (m n : ℕ) → is-equiv (id-to-iso m n)
    PDelta-is-univalent m n = is-eq _ g f-g g-f
      where Fin-m≃Fin-n : m ≊ n → Fin m ≃ Fin n
            Fin-m≃Fin-n (f' , mk-cat-equiv g' f-g g-f) = equiv (fst f') (fst g') (app= (fst= f-g)) (app= (fst= g-f))

            g : m ≊ n → m == n      
            g e = Fin-inj m n (ua (Fin-m≃Fin-n e))
             
            m≊m-is-contr : (m : ℕ) → is-contr (_≊_ {P = PDelta} m m)
            m≊m-is-contr m =
              let contr-wit = Σ-level (hom-is-contr _) λ _ →
                                      Σ-level (hom-is-contr _) λ _ →
                                              Σ-level (has-level-apply (raise-level _ (hom-is-contr _)) _ _) λ _ →
                                                      (has-level-apply (raise-level _ (hom-is-contr _)) _ _)
              in equiv-preserves-level (Σ-emap-r (Σ-is-cat-equiv)) ⦃ contr-wit ⦄

            f-g : id-to-iso m n ∘ g ∼ idf _
            f-g e with ℕ-trichotomy m n
            ... | inl idp = contr-has-all-paths ⦃ m≊m-is-contr m ⦄ _ _
            ... | inr (inl m<n) = (⊥-rec (Fin-inj-lemma m<n (! (ua (Fin-m≃Fin-n e)))))
            ... | inr (inr n<m) = (⊥-rec (Fin-inj-lemma n<m (ua (Fin-m≃Fin-n e))))
                        
            g-f : g ∘ id-to-iso m n ∼ idf _
            g-f _ = prop-has-all-paths _ _

    Delta : Category lzero lzero
    precat    Delta = PDelta
    univalent Delta = PDelta-is-univalent
