/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityTripleInnerFlat
public import FLT.Mazur.WeierstrassInfinityOutputComparison

/-!
# A two-input minor controls regularity of the infinity output

The existing integral projective cubic identity factors the cube of the input
XZ minor through the normalized output Z coordinate. Flat restriction to the
addition neighborhood preserves regularity, so regularity of this minor on the
original chart product would remove the remaining associativity obstruction.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassCurve

namespace FLT.Mazur.WeierstrassIntegralChart

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The XZ minor of the two original infinity chart inputs. -/
def infinityInputXZMinor : ChartProduct W 1 1 :=
  chartProductLeft W 1 1 (coord W 1 0) * chartProductRight W 1 1 (coord W 1 2) -
    chartProductRight W 1 1 (coord W 1 0) * chartProductLeft W 1 1 (coord W 1 2)

/-- The cube of the input minor factors through the actual polynomial output Z. -/
theorem infinityInputXZMinor_cube :
    infinityInputXZMinor W ^ 3 = chartProductAdditionCoordinates W 1 1 2 *
      (chartProductLeft W 1 1 (coord W 1 2) * chartProductRight W 1 1 (coord W 1 2)) := by
  exact (Projective.addZ_eq'
    (chartProductLeft_equation W 1 1 (AlgHom.id R _))
    (chartProductRight_equation W 1 1 (AlgHom.id R _))).symm

/-- The original product restricts flatly to the two-stage addition neighborhood. -/
theorem infinityAdditionRestriction_flat : (infinityAdditionRestriction W).toRingHom.Flat :=
  Flat.SpecMap_iff.mp (inferInstance : Flat (infinityAdditionInclusion W))

/-- A regular input minor gives a regular normalized output, with no difference inverted. -/
theorem infinityAdditionChart_z_regular_of_minor (h : IsRegular (infinityInputXZMinor W)) :
    IsRegular (infinityAdditionChart W (coord W 1 2)) := by
  have hp : IsRegular (chartProductAdditionCoordinates W 1 1 2) := by
    have hc := h.pow 3
    rw [infinityInputXZMinor_cube] at hc
    exact hc.of_mul_left
  have hr := flatRingHom_isRegular (infinityAdditionRestriction W).toRingHom
    (infinityAdditionRestriction_flat W) hp
  change IsRegular (infinityAdditionRestriction W (chartProductAdditionCoordinates W 1 1 2)) at hr
  rw [infinityPolynomial_scaled] at hr
  exact hr.of_mul_right

/-- This explicit two-input regularity target suffices on the genuine full triple member. -/
theorem infinityTripleFull_assoc_of_inputMinor_regular (hΔ : IsUnit W.Δ)
    (h : IsRegular (infinityInputXZMinor W)) :
    infinityTripleFullMap W hΔ ≫ integralCurveTripleAddLeft W hΔ =
      infinityTripleFullMap W hΔ ≫ integralCurveTripleAddRight W hΔ :=
  infinityTripleFull_assoc_of_law_output_regular W hΔ
    (infinityAdditionChart_z_regular_of_minor W h)

end FLT.Mazur.WeierstrassIntegralChart
