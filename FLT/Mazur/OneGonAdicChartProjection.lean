/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicChartRestriction

/-!
# Compatible projections onto the original affine Y chart

The adjacent finite charts retain the same projection onto the original
chart over the whole base ring. Both the full scalar map and every normalized
coordinate are preserved.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.OneGonAdicCharacterTower

open OneGonSmoothing WeierstrassIntegralChart AdicFormallySmoothStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [CommRing R] (I : Ideal R) (t : R) (m : ℕ)

/-- The original Y-chart ring mapped into its positive-order coefficient extension. -/
def chartProjectionRingMap : Coordinate (equation t) 1 →+*
    Coordinate (equation (parameter I t m)) 1 :=
  chartCoefficientRingMapTo (Ideal.Quotient.mk (I ^ (m + 1))) (equation t) 1
    (equation (parameter I t m)) (equation_map t (Ideal.Quotient.mk _))

/-- The projection from each finite chart to the original Y chart over the whole base. -/
def chartProjection : chartScheme (equation (parameter I t m)) 1 ⟶
    chartScheme (equation t) 1 :=
  Spec.map (CommRingCat.ofHom (chartProjectionRingMap I t m))

/-- Adjacent chart coefficients retain the original whole-base coordinate homomorphism. -/
theorem chartRestrictionRingMap_projection :
    (chartRestrictionRingMap I t m).comp (chartProjectionRingMap I t (m + 1)) =
      chartProjectionRingMap I t m := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro a
    change chartRestrictionRingMap I t m
      (chartProjectionRingMap I t (m + 1) (algebraMap R _ a)) =
        chartProjectionRingMap I t m (algebraMap R _ a)
    simp only [chartProjectionRingMap, chartRestrictionRingMap,
      chartCoefficientRingMapTo_scalar]
    rfl
  · intro i
    change chartRestrictionRingMap I t m
      (chartProjectionRingMap I t (m + 1) (coord (equation t) 1 i)) =
        chartProjectionRingMap I t m (coord (equation t) 1 i)
    simp only [chartProjectionRingMap, chartRestrictionRingMap,
      chartCoefficientRingMapTo_coord]

/-- The actual adjacent chart restriction preserves the projection to the original Y chart. -/
@[reassoc] theorem chartRestriction_projection :
    chartRestriction I t m ≫ chartProjection I t (m + 1) = chartProjection I t m := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, chartRestrictionRingMap_projection]

end FLT.Mazur.OneGonAdicCharacterTower
