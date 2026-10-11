/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitNodalTangentEvaluation

/-!
# Actual addition preserves and scales both infinitesimal node branches

On the tangent `y = 0`, X scales by `r/q`; on `y + a*x = 0`, it scales by `q/r`.
These are evaluations of the original addition map, with the original branch order.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (a : Rˣ) (r q : Sˣ) (x y : S)
  (hq : (q : S) = (r : S) + algebraMap R S a)
  (hxx : x ^ 2 = 0) (hxy : x * y = 0) (hyy : y ^ 2 = 0)
local notation "W" => WeierstrassCurve.mk (a : R) 0 0 0 0
local notation "O" => splitNodalTangentOutput (a : R) r q x y hq hxx hxy hyy

/-- The first original tangent branch remains the first branch under actual addition. -/
theorem splitNodalTangentOutput_first_branch (hy : y = 0) : O (coord W 2 1) = 0 := by
  rw [splitNodalTangentOutput_first_scaling, hy, mul_zero]

/-- The complete first-order X coordinate on the first branch has reciprocal character. -/
theorem splitNodalTangentOutput_first_branch_x (hy : y = 0) :
    O (coord W 2 0) = (↑(r * q⁻¹) : S) * x := by
  have hy' := splitNodalTangentOutput_first_branch a r q x y hq hxx hxy hyy hy
  have hx := splitNodalTangentOutput_second_scaling (a : R) r q x y hq hxx hxy hyy
  simp only [map_add, map_mul, AlgHom.commutes] at hx
  have hi : y + algebraMap R S a * x = algebraMap R S a * x := by rw [hy, zero_add]
  rw [hy', hi, zero_add] at hx
  apply (a.isUnit.map (algebraMap R S)).mul_right_inj.mp
  exact hx.trans (by ring)

/-- The opposite original tangent branch also remains unchanged as a branch. -/
theorem splitNodalTangentOutput_second_branch (hy : y + algebraMap R S a * x = 0) :
    O (coord W 2 1 + algebraMap R (Coordinate W 2) a * coord W 2 0) = 0 := by
  rw [splitNodalTangentOutput_second_scaling, hy, mul_zero]

/-- The X coordinate on the opposite tangent branch has the original Laurent character. -/
theorem splitNodalTangentOutput_second_branch_x (hy : y + algebraMap R S a * x = 0) :
    O (coord W 2 0) = (↑(q * r⁻¹) : S) * x := by
  have hc := splitNodalTangentOutput_second_branch a r q x y hq hxx hxy hyy hy
  simp only [map_add, map_mul, AlgHom.commutes] at hc
  have hy' := splitNodalTangentOutput_first_scaling (a : R) r q x y hq hxx hxy hyy
  apply (a.isUnit.map (algebraMap R S)).mul_right_inj.mp
  linear_combination hc - hy' - (↑(q * r⁻¹) : S) * hy

end FLT.Mazur.WeierstrassIntegralChart
