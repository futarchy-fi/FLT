/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitNodalTangentEvaluation
public import FLT.Mazur.WeierstrassSplitNodalUnitPoints

/-!
# Tangent characters in the original Laurent coordinate

The ratio `q/r` is exactly the Laurent unit of the smooth Y-chart parameter.
Thus the two actual tangent branch functions have characters `t` and `t⁻¹`.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (a : Rˣ) (r q : Sˣ)
  (e : Coordinate (splitNodalEquation a) 1 →ₐ[R] S)
  (hq : (q : S) = (r : S) + algebraMap R S a)
  (he : e (coord (splitNodalEquation a) 1 0) = (↑r⁻¹ : S))

include hq he

/-- The normalized affine slope determines precisely the original Laurent unit. -/
theorem splitNodalTangentParameter_laurent : splitNodalChartUnit a e = q * r⁻¹ := by
  apply Units.ext
  change e (splitNodalLaurentToChart a (LaurentPolynomial.T 1)) = _
  rw [splitNodalLaurentToChart_pos, map_add, map_one, map_mul, e.commutes, he,
    Units.val_mul, hq]
  have h := Units.mul_inv r
  linear_combination -h

variable (x y : S) (hxx : x ^ 2 = 0) (hxy : x * y = 0) (hyy : y ^ 2 = 0)
local notation "W" => splitNodalEquation a
local notation "O" => splitNodalTangentOutput (a : R) r q x y hq hxx hxy hyy

/-- The first branch character of genuine addition is the original smooth Laurent parameter. -/
theorem splitNodalTangentOutput_laurent_first :
    O (coord W 2 1) = (splitNodalChartUnit a e : S) * y := by
  rw [splitNodalTangentParameter_laurent a r q e hq he]
  exact splitNodalTangentOutput_first_scaling (a : R) r q x y hq hxx hxy hyy

/-- The opposite branch character is its inverse, with the original tangent ordering. -/
theorem splitNodalTangentOutput_laurent_second :
    O (coord W 2 1 + algebraMap R (Coordinate W 2) (a : R) * coord W 2 0) =
      (↑(splitNodalChartUnit a e)⁻¹ : S) * (y + algebraMap R S a * x) := by
  rw [splitNodalTangentParameter_laurent a r q e hq he]
  have h : (q * r⁻¹)⁻¹ = r * q⁻¹ := by simp only [mul_inv_rev, inv_inv]
  rw [h]
  exact splitNodalTangentOutput_second_scaling (a : R) r q x y hq hxx hxy hyy

end FLT.Mazur.WeierstrassIntegralChart
