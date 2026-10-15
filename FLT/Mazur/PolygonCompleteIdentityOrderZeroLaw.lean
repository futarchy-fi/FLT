/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFiniteReduction
public import FLT.Mazur.PolygonCompleteIdentityFiniteLawCriterion

/-!
# Original Laurent multiplication and the full cubic comparison at order zero

The coefficientwise nilpotence bound is one at order zero, so the original
multiplication error is zero. The full original cubic comparison follows,
including the nodes, from the proved schematic detection criterion.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonInfinitesimal
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The full original multiplication error vanishes at order zero. -/
theorem completeIdentityFiniteMulDefect_zero (i : Fin n) :
    completeIdentityFiniteMulDefect K n h i 0 = 0 := by
  ext a b
  simpa only [zero_add, pow_one, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using
    completeIdentityFiniteMulDefect_coeff_pow K n h i 0 a b

/-- The actual original multiplication unit has exactly the product formula at order zero. -/
theorem completeIdentityFiniteMulUnit_zero (i : Fin n) :
    completeIdentityFiniteMulUnit K n h i 0 =
      Units.map (LaurentPolynomial.C : (Ring K 0)[T;T⁻¹] →+*
        (Ring K 0)[T;T⁻¹][T;T⁻¹])
        (PolygonUniversalScaling.u (R := Ring K 0)) * PolygonUniversalScaling.u := by
  apply Units.ext
  have he := completeIdentityFiniteMulDefect_zero K n h i
  rw [completeIdentityFiniteMulDefect, sub_eq_zero] at he
  simpa [PolygonUniversalScaling.u, PolygonChartScaling.coordinateUnit] using he

/-- Original multiplication equals Laurent multiplication at order zero in every identity chart. -/
theorem completeIdentityFiniteLaw_zero (i : Fin n) :
    universalEdgeScaling (Ring K 0) ≫ completeIdentityStageTorus K n h i 0 =
      completeIdentityFiniteOriginalMul K n h i 0 :=
  (completeIdentityFiniteLaw_iff_unit K n h i 0).mpr
    (completeIdentityFiniteMulUnit_zero K n h i)

/-- At order zero the entire original finite cubic action agrees, including every node. -/
theorem completeIdentityFiniteComparison_zero :
    completeIdentityFiniteScaling K n h 0 ≫ completePointToIntegralCubic K n h 0 =
      completeIdentityFiniteInput K n h 0 0 ≫ completeIdentityActionTarget K n h 0 :=
  (completeIdentityFiniteComparison_iff_laurentLaw K n h 0).mpr
    (completeIdentityFiniteLaw_zero K n h 0)

end FLT.Mazur.PolygonInfinitesimalStages
