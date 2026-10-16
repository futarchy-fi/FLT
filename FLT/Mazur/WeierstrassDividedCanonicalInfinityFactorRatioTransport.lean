/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedCanonicalInfinityFactorRatio
public import FLT.Mazur.WeierstrassModificationXCoefficientTransport

/-!
# Independently named coefficient targets for full infinity polygon maps

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
  (h3a : W.a₃ ∈ I) (h4a : W.a₄ ∈ I) (h6a : W.a₆ ∈ I)
  (h3a' : U.a₃ ∈ J) (h4a' : U.a₄ ∈ J) (h6a' : U.a₆ ∈ J)
  (h2' : U.a₂ ∈ J) (h3' : c3 ∈ J) (h4' : c4 ∈ J) (h6' : c6 ∈ J)
  [Fact (IsNilpotent (initialTangentSmoothing W ha s))]
  [Fact (IsNilpotent (initialTangentSmoothing U ha' s'))] (k : ℕ)
attribute [local irreducible] canonicalFactorRatioInfinityPolygonMap
include hf hB3 hB4 hB6

/-- Explicit coefficient targets preserve the complete canonical regular infinity square. -/
@[reassoc] theorem canonicalFactorRatioInfinityPolygonMap_coefficient_of_eq :
    canonicalFactorRatioInfinityPolygonMap U ha' s' c3 c4 c6 J hJ h2' h3' h4' h6' h3a' h4a' h6a' k ≫
      PolygonInfinitesimal.parameterProjection f (initialTangentSmoothing W ha s)
        (initialTangentSmoothing U ha' s')
        (initialTangentSmoothing_mapTo f W ha s U ha' s' hW hs) (2 * k + 3) (by omega) =
      Spec.map (CommRingCat.ofHom
        (WeierstrassIntegralChart.chartCoefficientRingMapTo f W 1 U hW)) ≫
          canonicalFactorRatioInfinityPolygonMap W ha s b3 b4 b6 I hI
            h2 h3 h4 h6 h3a h4a h6a k := by
  subst U s' c3 c4 c6
  exact canonicalFactorRatioInfinityPolygonMap_coefficient W ha s b3 b4 b6
    I hI h2 h3 h4 h6 h3a h4a h6a k f J hf hJ

end FLT.Mazur.WeierstrassDividedDepth
