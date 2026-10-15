/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeTrivializedChartGeometry

/-!
# The scalar correction at each natural arithmetic component label

The identity has scale one, labels strictly below the midpoint have the original
tangent scale, and the other labels have its signed inverse at complementary depth.
This includes the single even midpoint, with no duplicate component.
-/

@[expose] public noncomputable section
open AlgebraicGeometry IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
universe u
variable {K : Type u} [Field K] {A : ValuationSubring K}
  {W : WeierstrassCurve A} {π : A} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (r : (ResidueField A)ˣ)

/-- The full Laurent scale attached to a natural cyclic label. -/
def resolvedCyclicCoordinateScale (i : ℕ) : (ResidueField A)ˣ :=
  if i = 0 then 1 else if 2 * i < depth then nodeLaurentScale D r i
    else (-nodeLaurentScale D r (depth - i))⁻¹

/-- The reciprocal identity is already in the closed cycle's coordinate. -/
@[simp] theorem resolvedCyclicCoordinateScale_zero : resolvedCyclicCoordinateScale D r 0 = 1 := by
  simp only [resolvedCyclicCoordinateScale, ite_true]

/-- Every positive branch strictly below the midpoint has its original tangent scale. -/
theorem resolvedCyclicCoordinateScale_positive (i : ℕ) (hi : 0 < i) (hp : 2 * i < depth) :
    resolvedCyclicCoordinateScale D r i = nodeLaurentScale D r i := by
  rw [resolvedCyclicCoordinateScale, ite_eq_right (by omega), ite_eq_left hp]

/-- The negative branch at complementary depth keeps the signed inverse tangent scale. -/
theorem resolvedCyclicCoordinateScale_negative (j : ℕ) (hj : 0 < j) (hp : 2 * j ≤ depth) :
    resolvedCyclicCoordinateScale D r (depth - j) = (-nodeLaurentScale D r j)⁻¹ := by
  rw [resolvedCyclicCoordinateScale, ite_eq_right (by omega), ite_eq_right (by omega),
    Nat.sub_sub_self (by omega)]

/-- The even midpoint uses the negative-coordinate convention of the original middle chart. -/
theorem resolvedCyclicCoordinateScale_middle (j : ℕ) (hj : 0 < j) (hp : 2 * j = depth) :
    resolvedCyclicCoordinateScale D r j = (-nodeLaurentScale D r j)⁻¹ := by
  have he : depth - j = j := by omega
  simpa only [he] using resolvedCyclicCoordinateScale_negative D r j hj (by omega)

end FLT.Mazur.WeierstrassDividedDepth
