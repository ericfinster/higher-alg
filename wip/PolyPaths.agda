{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import PolyMonad

module wip.PolyPaths {ℓ} where

  -- Some lemmas about polynomials which are equal.

 W→ : {I J : Type ℓ} {P : Poly I} {Q : Poly J}
   → (p : (I , P) == (J , Q))
   → (i : I) → W P i → W Q (–> (coe-equiv (fst= p)) i)
 W→ idp i w = w

 PolyType : Type (lsucc ℓ)
 PolyType = Σ (Type ℓ) Poly

 RelType : PolyType → Type (lsucc ℓ)
 RelType (I , P) = PolyRel P

 MgmType : PolyType → Type ℓ
 MgmType (I , P) = PolyMagma P

 SubInvarType : Σ PolyType RelType → Type ℓ
 SubInvarType (_ , R) = SubInvar R

 --
 --  Some silly and trivial facts using
 --  id elimination for polynomials
 --
 
 Slice↓ : {I J : Type ℓ} {P : Poly I} {Q : Poly J}
   → (p : (I , P) == (J , Q))
   → {R : PolyRel P} {S : PolyRel Q}
   → (q : R == S [ RelType ↓ p ])
   → Path {A = PolyType} (Ops P , (P // R)) (Ops Q , (Q // S))
 Slice↓ idp idp = idp

 SubInvar-transp : {I J : Type ℓ} {P : Poly I} {Q : Poly J}
   → (p : (I , P) == (J , Q))
   → {R : PolyRel P} {S : PolyRel Q}
   → (q : R == S [ RelType ↓ p ])
   → SubInvar R → SubInvar S
 SubInvar-transp idp idp Ψ = Ψ

 SubInvar-transp! : {I J : Type ℓ} {P : Poly I} {Q : Poly J}
   → (p : (I , P) == (J , Q))
   → {R : PolyRel P} {S : PolyRel Q}
   → (q : R == S [ RelType ↓ p ])
   → SubInvar S → SubInvar R
 SubInvar-transp! idp idp Ψ = Ψ

 SubInvar-po! : {I J : Type ℓ} {P : Poly I} {Q : Poly J}
   → (p : (I , P) == (J , Q))
   → {R : PolyRel P} {S : PolyRel Q}
   → (q : R == S [ RelType ↓ p ])
   → (Ψ : SubInvar S)
   → SubInvar-transp! p q Ψ == Ψ [ SubInvarType ↓ pair= p q ]
 SubInvar-po! idp idp Ψ = idp

 CohStruct-transp! : {I J : Type ℓ} {P : Poly I} {Q : Poly J}
   → (p : (I , P) == (J , Q))
   → {R : PolyRel P} {S : PolyRel Q}
   → (q : R == S [ RelType ↓ p ])
   → {ΨR : SubInvar R} {ΨS : SubInvar S}
   → (r : ΨR == ΨS [ SubInvarType ↓ pair= p q ])
   → CohStruct (SlcMgm ΨS) → CohStruct (SlcMgm ΨR)
 CohStruct-transp! idp idp idp C = C
