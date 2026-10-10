/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassOriginIdealSheaf

/-!
# Automorphisms preserve the intrinsic origin powers

Fixing the original zero morphism preserves its full scheme-theoretic ideal,
and therefore every power. No reduction, coordinate shape, or invariance of
the chosen parameter neighborhood is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
  (e : integralCurve W ≅ integralCurve W)
  (hz : integralCurveZero W ≫ e.hom = integralCurveZero W)

include hz in
/-- Every automorphism fixing the actual origin preserves its scheme-theoretic ideal. -/
theorem originAut_ideal_invariant :
    (integralCurveZero W).ker.comap e.hom = (integralCurveZero W).ker := by
  have h := ProjectiveLineMarkedCharts.ker_comap_mono (integralCurveZero W) e.hom
  rwa [hz] at h

include hz in
/-- The actual automorphism preserves every intrinsic origin power. -/
theorem originAut_ideal_power_invariant (n : ℕ) :
    ((integralCurveZero W).ker ^ n).comap e.hom = (integralCurveZero W).ker ^ n := by
  rw [FCurve.idealSheaf_comap_pow, originAut_ideal_invariant W e hz]

include hz in
/-- Pullback along any chart and its actual moved chart gives the same origin power. -/
theorem originAut_ideal_power_chart {T : Scheme.{u}} (f : T ⟶ integralCurve W) (n : ℕ) :
    ((integralCurveZero W).ker ^ n).comap (f ≫ e.hom) =
      ((integralCurveZero W).ker ^ n).comap f := by
  rw [Scheme.IdealSheafData.comap_comp, originAut_ideal_power_invariant W e hz]

include hz in
/-- On the actual moved neighborhood the intrinsic ideal still has the original local equation. -/
theorem originAut_ideal_power_neighborhood (n : ℕ) :
    ((integralCurveZero W).ker ^ n).comap (originNeighborhoodInclusion W ≫ e.hom) =
      (originNeighborhoodSection W).ker ^ n := by
  rw [originAut_ideal_power_chart W e hz, originIdealSheaf_power_neighborhood]

end FLT.Mazur.WeierstrassIntegralChart
