/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitNodalAffineParameters

/-!
# Unit parameters from actual common affine and Y-chart inputs

Cross-coordinate identities recover unit slope parameters directly from chart
homomorphisms over arbitrary rings. The recovered Laurent parameter is exactly
the original tangent coordinate, rather than an auxiliary point label.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (a : Rˣ)

/-- The unit represented by a Y-chart point is its actual tangent coordinate. -/
theorem splitNodalChartUnit_val (p : Coordinate (splitNodalEquation a) 1 →ₐ[R] S) :
    (splitNodalChartUnit a p : S) =
      1 + algebraMap R S a * p (coord (splitNodalEquation a) 1 0) := by
  change p (splitNodalLaurentToChart a (LaurentPolynomial.T 1)) = _
  rw [splitNodalLaurentToChart_pos, map_add, map_one, map_mul, AlgHom.commutes]

/-- A common affine and Y-chart point has a unit slope inverse to its normalized X. -/
theorem splitNodalAffineChart_exists_parameter
    (f : Coordinate (splitNodalEquation a) 2 →ₐ[R] S)
    (p : Coordinate (splitNodalEquation a) 1 →ₐ[R] S)
    (h : ∀ i, f (coord (splitNodalEquation a) 2 i) =
      f (coord (splitNodalEquation a) 2 1) * p (coord (splitNodalEquation a) 1 i)) :
    ∃ r : Sˣ, IsUnit ((r : S) + algebraMap R S a) ∧
      f (coord (splitNodalEquation a) 2 0) = (r : S) * ((r : S) + algebraMap R S a) ∧
      f (coord (splitNodalEquation a) 2 1) = (r : S) ^ 2 * ((r : S) + algebraMap R S a) ∧
      (r : S) * p (coord (splitNodalEquation a) 1 0) = 1 := by
  have h2 := h 2
  rw [coord_self, map_one] at h2
  have hy := isUnit_of_mul_isUnit_left (h2 ▸ isUnit_one)
  obtain ⟨r, hra, hx, hyr⟩ :=
    splitNodalAffine_exists_parameter (splitNodalAffine_algebra_equation a f) hy
  refine ⟨r, hra, hx, hyr, ?_⟩
  have hr : (r : S) * f (coord (splitNodalEquation a) 2 0) =
      f (coord (splitNodalEquation a) 2 1) := by rw [hx, hyr]; ring
  apply hy.mul_right_inj.mp
  linear_combination -(r : S) * h 0 + hr

/-- The unit slope formula gives precisely the Laurent chart unit. -/
theorem splitNodalChartUnit_mul_slope
    (p : Coordinate (splitNodalEquation a) 1 →ₐ[R] S) (r : S)
    (hr : r * p (coord (splitNodalEquation a) 1 0) = 1) :
    r * (splitNodalChartUnit a p : S) = r + algebraMap R S a := by
  rw [splitNodalChartUnit_val]
  linear_combination algebraMap R S a * hr

end FLT.Mazur.WeierstrassIntegralChart
