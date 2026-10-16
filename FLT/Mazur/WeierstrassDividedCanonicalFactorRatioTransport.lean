/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedCanonicalFactorRatioNaturality
public import FLT.Mazur.WeierstrassModificationXCoefficientTransport

/-!
# Independently named coefficient targets for full affine polygon maps

The lower-order curve and all divided coefficients may be constructed separately.
Transport uses the original coefficient ring map and the exact normalized smoothing.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
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
  [Fact (IsNilpotent (initialTangentSmoothing W ha s))]
  [Fact (IsNilpotent (initialTangentSmoothing U ha' s'))] (k : ℕ)
attribute [local irreducible] canonicalFactorRatioAffinePolygonMap
include hf

/-- Explicit coefficient targets preserve the complete canonical glued affine square. -/
@[reassoc] theorem canonicalFactorRatioAffinePolygonMap_coefficient_of_eq :
    canonicalFactorRatioAffinePolygonMap U ha' s' c3 c4 c6 J hJ h2' h3' h4' h6' k ≫
      PolygonInfinitesimal.parameterProjection f (initialTangentSmoothing W ha s)
        (initialTangentSmoothing U ha' s')
        (initialTangentSmoothing_mapTo f W ha s U ha' s' hW hs) (2 * k + 3) (by omega) =
      Spec.map (CommRingCat.ofHom
        (coefficientRingMapTo f W s b3 b4 b6 U s' c3 c4 c6 hW hs hB3 hB4 hB6)) ≫
          canonicalFactorRatioAffinePolygonMap W ha s b3 b4 b6 I hI h2 h3 h4 h6 k := by
  subst U s' c3 c4 c6
  exact canonicalFactorRatioAffinePolygonMap_coefficient f W ha s b3 b4 b6
    I J hf hI hJ h2 h3 h4 h6 k

end FLT.Mazur.WeierstrassDividedDepth
