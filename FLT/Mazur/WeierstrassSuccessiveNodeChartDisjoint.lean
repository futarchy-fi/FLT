/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveNodeChartCoverage

/-!
# The original complete polygon branches are disjoint

The full simple-root polygon charts inherit separation from their actual
quadratic evaluation maps, including over nonreduced coefficient rings.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
  (r : SuccessiveIncidence.Coordinate π)
  (hr : r ^ 2 + nodeSlopeLinear W π b3 * r = nodeSlopeConstant W s π b4 b6)
  (hu : IsUnit (r + r + nodeSlopeLinear W π b3))
local notation "a" => nodeSlopeLinear W π b3
local notation "b" => nodeSlopeConstant W s π b4 b6

include hu in
/-- The complete polygon charts of the two simple roots have disjoint images. -/
theorem simpleSlopePolygonCharts_disjoint :
    Disjoint (Set.range (simpleSlopePolygonChart W s π b3 b4 b6 r hr))
      (Set.range (simpleSlopePolygonChart W s π b3 b4 b6
        (QuadraticRootBranchLocalization.oppositeRoot a r)
        (QuadraticRootBranchLocalization.oppositeRoot_equation a b r hr))) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
  let e := PrimeSpectrum.comapEquiv (monicEquiv W s π b3 b4 b6).toRingEquiv
  have hinj : Function.Injective
      (PrimeSpectrum.comap (toMonic W s π b3 b4 b6).toRingHom) := e.symm.injective
  change PrimeSpectrum.comap (toMonic W s π b3 b4 b6).toRingHom
    (PrimeSpectrum.comap (QuadraticRootBranchLocalization.evaluation a b
      (QuadraticRootBranchLocalization.oppositeRoot a r)
      (QuadraticRootBranchLocalization.oppositeRoot_equation a b r hr)).toRingHom
      (PrimeSpectrum.comap (SuccessiveIncidence.toPolygon π).toRingHom y)) =
    PrimeSpectrum.comap (toMonic W s π b3 b4 b6).toRingHom
      (PrimeSpectrum.comap (QuadraticRootBranchLocalization.evaluation a b r hr).toRingHom
        (PrimeSpectrum.comap (SuccessiveIncidence.toPolygon π).toRingHom x)) at hy
  have he := hinj hy
  exact Set.disjoint_left.mp
    (QuadraticRootBranchLocalization.rootCharts_disjoint a b r hr hu)
    ⟨PrimeSpectrum.comap (SuccessiveIncidence.toPolygon π).toRingHom x, rfl⟩
    ⟨PrimeSpectrum.comap (SuccessiveIncidence.toPolygon π).toRingHom y, he⟩

variable (I : Ideal R) (hI : IsNilpotent I) (ha : IsUnit W.a₁) (hs : s ∈ I) (h2 : W.a₂ ∈ I)
  (h3 : b3 ∈ I) (h4 : b4 ∈ I) (h6 : b6 ∈ I)

/-- The full constructed small and opposite polygon node charts never meet. -/
theorem nilpotentPolygonCharts_disjoint :
    Disjoint (Set.range (nilpotentPolygonChart W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6))
      (Set.range (oppositePolygonChart W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6)) := by
  have he : simpleSlopeRetraction W s π b3 b4 b6
      (nilpotentNodeSlope W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6)
      (nilpotentNodeSlope_equation W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6) =
        nilpotentNodeRetraction W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6 :=
    nilpotentNodeRetraction_monic W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6
  have h := simpleSlopePolygonCharts_disjoint W s π b3 b4 b6 _
    (nilpotentNodeSlope_equation W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6)
    (nilpotentNodeSlope_simple W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6)
  simpa only [simpleSlopePolygonChart, he, nilpotentPolygonChart, nilpotentNodeChart,
    oppositePolygonChart, oppositeNodeSlope] using h

end FLT.Mazur.WeierstrassSuccessiveX
