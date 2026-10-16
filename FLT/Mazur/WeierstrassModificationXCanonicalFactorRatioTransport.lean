/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXCanonicalFactorRatioChart
public import FLT.Mazur.WeierstrassModificationXArithmeticInitialMobius

/-!
# Explicit coefficient targets for canonical corrected polygon charts

The target curve and coefficients can be independently named, as they are in
consecutive arithmetic quotients. The canonical roots remain independently constructed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  (W : WeierstrassCurve R) (ha : IsUnit W.a₁) (s b3 b4 b6 : R)
  (U : WeierstrassCurve S) (ha' : IsUnit U.a₁) (s' c3 c4 c6 : S)
  (hW : W.map f = U) (hs : f s = s') (hB3 : f b3 = c3)
  (hB4 : f b4 = c4) (hB6 : f b6 = c6)
  (I : Ideal R) (J : Ideal S) (hf : I ≤ J.comap f)
  (hI : IsNilpotent I) (hJ : IsNilpotent J)
  (h2 : W.a₂ ∈ I) (h3 : b3 ∈ I) (h4 : b4 ∈ I) (h6 : b6 ∈ I)
  (h2' : U.a₂ ∈ J) (h3' : c3 ∈ J) (h4' : c4 ∈ J) (h6' : c6 ∈ J)
attribute [local irreducible] canonicalFactorRatioChart
include hf hB3 hB4 hB6

/-- The whole corrected canonical chart commutes with explicitly identified target data. -/
@[reassoc] theorem canonicalFactorRatioChart_coefficient_of_eq :
    Spec.map (CommRingCat.ofHom (nodeOpenCoefficientRingMapTo f W s U s' hW hs)) ≫
      canonicalFactorRatioChart W ha s b3 b4 b6 I hI h2 h3 h4 h6 =
        canonicalFactorRatioChart U ha' s' c3 c4 c6 J hJ h2' h3' h4' h6' ≫
          Spec.map (CommRingCat.ofHom (PolygonSmoothing.ringMap f
            (initialTangentSmoothing W ha s) (initialTangentSmoothing U ha' s')
            (initialTangentSmoothing_mapTo f W ha s U ha' s' hW hs))) := by
  subst U s' c3 c4 c6
  exact canonicalFactorRatioChart_coefficient W ha s b3 b4 b6 I hI h2 h3 h4 h6 f J hf hJ

end FLT.Mazur.WeierstrassModificationX
