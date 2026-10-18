/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityCubicInverse
public import FLT.Mazur.WeierstrassSplitNodalLaurent

/-!
# Laurent coordinates for the full nilpotent infinity cubic

The horizontal coordinate is the split tangent expression. Finite iteration
constructs the vertical coordinate with every original cubic coefficient.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (ha : IsUnit W.a₁)
  (I : Ideal R) (hI : IsNilpotent I)
  (h2 : W.a₂ ∈ I) (h3 : W.a₃ ∈ I) (h4 : W.a₄ ∈ I) (h6 : W.a₆ ∈ I)
local notation "L" => R[T;T⁻¹]
local notation "B" => Coordinate W 1
local notation "x" => splitNodalLaurentX ha.unit

/-- The chosen horizontal coordinate has the positive Laurent tangent factor. -/
theorem nilpotentInfinityLaurent_tangent :
    1 + algebraMap R L W.a₁ * x = LaurentPolynomial.T 1 := by
  simpa only [ha.unit_spec] using splitNodalLaurent_tangent ha.unit

/-- The linear coefficient of the vertical cubic is a unit. -/
theorem nilpotentInfinityLaurent_tangent_isUnit :
    IsUnit (1 + algebraMap R L W.a₁ * x) := by
  rw [nilpotentInfinityLaurent_tangent]
  exact LaurentPolynomial.isUnit_T 1

/-- The full vertical Laurent coordinate, constructed rather than supplied. -/
def nilpotentInfinityLaurentZ : L :=
  infinityVerticalSolution W I hI h2 h3 h4 h6 x
    (nilpotentInfinityLaurent_tangent_isUnit W ha)

local notation "z" => nilpotentInfinityLaurentZ W ha I hI h2 h3 h4 h6

/-- These Laurent coordinates satisfy the original cubic, including all nilpotent terms. -/
theorem nilpotentInfinityLaurent_equation :
    (W.map (algebraMap R L)).toProjective.Equation ![x, 1, z] := by
  rw [WeierstrassCurve.Projective.equation_iff]
  simp only [WeierstrassCurve.map, WeierstrassCurve.toProjective,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    one_pow, one_mul, mul_one]
  change z + algebraMap R L W.a₁ * x * z + algebraMap R L W.a₃ * z ^ 2 -
    (x ^ 3 + algebraMap R L W.a₂ * x ^ 2 * z +
      algebraMap R L W.a₄ * x * z ^ 2 + algebraMap R L W.a₆ * z ^ 3) = 0
  have h := infinityVerticalSolution_equation W I hI h2 h3 h4 h6 x
    (nilpotentInfinityLaurent_tangent_isUnit W ha)
  change z * (1 + algebraMap R L W.a₁ * x + algebraMap R L W.a₃ * z -
    algebraMap R L W.a₂ * x ^ 2 - algebraMap R L W.a₄ * x * z -
    algebraMap R L W.a₆ * z ^ 2) = x ^ 3 at h
  linear_combination h

/-- Evaluation from the full cubic chart into the Laurent algebra. -/
def nilpotentInfinityChartToLaurent : B →ₐ[R] L :=
  evaluation W 1 ![x, 1, z]
    (nilpotentInfinityLaurent_equation W ha I hI h2 h3 h4 h6) rfl

/-- Evaluation retains the constructed coordinates. -/
@[simp] theorem nilpotentInfinityChartToLaurent_coord (i : Fin 3) :
    nilpotentInfinityChartToLaurent W ha I hI h2 h3 h4 h6 (coord W 1 i) =
      ![x, 1, z] i := evaluation_coord _ _ _ _ _ i

/-- The tangent factor is a unit on the full original nilpotent chart. -/
def nilpotentInfinityTangentUnit : Bˣ :=
  (nilpotentInfinityLinear_isUnit W I hI h2 h3 h4 h6).unit

/-- The tangent unit has the exact original linear expression. -/
theorem nilpotentInfinityTangentUnit_val :
    (nilpotentInfinityTangentUnit W I hI h2 h3 h4 h6 : B) =
      1 + algebraMap R B W.a₁ * coord W 1 0 := IsUnit.unit_spec _

/-- The reverse map is evaluation at the actual tangent unit. -/
def nilpotentInfinityLaurentToChart : L →ₐ[R] B :=
  LaurentUnitPoints.evalUnit (nilpotentInfinityTangentUnit W I hI h2 h3 h4 h6)

/-- The positive generator recovers the full linear tangent factor. -/
theorem nilpotentInfinityLaurentToChart_pos :
    nilpotentInfinityLaurentToChart W I hI h2 h3 h4 h6 (LaurentPolynomial.T 1) =
      1 + algebraMap R B W.a₁ * coord W 1 0 := by
  simp only [nilpotentInfinityLaurentToChart, LaurentUnitPoints.evalUnit_T, zpow_one,
    nilpotentInfinityTangentUnit_val]

/-- The reverse map recovers the horizontal coordinate on the entire chart. -/
theorem nilpotentInfinityLaurentToChart_x :
    nilpotentInfinityLaurentToChart W I hI h2 h3 h4 h6 x = coord W 1 0 := by
  rw [splitNodalLaurentX, map_mul, AlgHom.commutes, map_sub, map_one,
    nilpotentInfinityLaurentToChart_pos, add_sub_cancel_left,
    ← mul_assoc, ← map_mul, ha.val_inv_mul, map_one, one_mul]

end FLT.Mazur.WeierstrassIntegralChart
