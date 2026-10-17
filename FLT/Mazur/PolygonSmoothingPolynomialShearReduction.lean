/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonSmoothingNilpotentShear
public import FLT.Mazur.PolygonSmoothingSquareZeroEdgeFactors
public import FLT.Mazur.PolygonSmoothingScalingNaturality

/-!
# Recovery of the original whole-node shear

On a layer annihilating the smoothing, every outgoing polynomial equals its
constant coefficient after weighting by the opposite coordinate. Consequently
the compensating inverse in the nilpotent lift fixes that coordinate exactly.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonSmoothing
open LaurentPolynomial
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (t e : R) (het : e * t = 0)
local notation "A" => ChartRing t
local notation "E" => algebraMap R A e
local notation "x" => leftCoordinate t
local notation "y" => rightCoordinate t

include het in
/-- The opposite weighted coordinate kills every nonconstant outgoing polynomial term. -/
theorem outgoingPolynomialLift_weighted_right (q : R[T;T⁻¹]) :
    E * y * outgoingPolynomialLift t q = E * y * algebraMap R A (q.coeff 0) := by
  have hEt : E * algebraMap R A t = 0 := by rw [← map_mul, het, map_zero]
  induction q using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    simp only [outgoingPolynomialLift_add, AddMonoidAlgebra.coeff_add,
      Finsupp.add_apply, map_add, mul_add, hp, hq]
  | C_mul_T n r =>
    rw [outgoingPolynomialLift_integer, ← single_eq_C_mul_T]
    simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    by_cases hn : n = 0
    · subst n
      simp
    · rw [ite_eq_right hn]
      by_cases hn0 : 0 ≤ n
      · rw [ite_eq_left hn0, map_zero, mul_zero]
        obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero
          (show n.toNat ≠ 0 by omega)
        rw [hk, pow_succ]
        calc
          _ = (E * (x * y)) * (algebraMap R A r * x ^ k) := by ring
          _ = 0 := by rw [coordinate_relation, hEt, zero_mul]
      · rw [ite_eq_right hn0, mul_zero, map_zero, mul_zero]

include het in
/-- The constant coefficient of the boundary lift is the original linear coefficient. -/
theorem boundaryLift_weighted_right (q : R[T;T⁻¹]) :
    E * y * LaurentBoundaryCorrectionSplit.boundaryLift t q =
      E * y * algebraMap R A (q.coeff 1) := by
  rw [LaurentBoundaryCorrectionSplit.boundaryLift,
    outgoingPolynomialLift_weighted_right t e het, LaurentBoundaryCorrectionSplit.shifted_coeff]
  norm_num

include het in
/-- The smoothing drift vanishes on every layer annihilating the smoothing. -/
theorem nilpotentShear_parameter_eq (c : R) : (1 + e * c) * t = t := by
  calc
    _ = t + c * (e * t) := by ring
    _ = t := by rw [het, mul_zero, add_zero]

/-- The inverse multiplier cancels on the opposite coordinate for the polynomial lift. -/
theorem nilpotentShearEquiv_right_fixed (he : IsNilpotent e) (c : R) (p : A)
    (hp : E * y * p = E * y * algebraMap R A c) :
    nilpotentShearEquiv t e he c p (rightCoordinate ((1 + e * c) * t)) = y := by
  rw [nilpotentShearEquiv_right]
  have hv : algebraMap R A (1 + e * c) * y =
      y * (nilpotentChartMultiplier t e he p : A) := by
    rw [nilpotentChartMultiplier_val, map_add, map_one, map_mul]
    linear_combination -hp
  calc
    _ = (algebraMap R A (1 + e * c) * y) *
        ↑(nilpotentChartMultiplier t e he p)⁻¹ := by ring
    _ = y := by rw [hv, mul_assoc, Units.mul_inv, mul_one]

/-- The nilpotent lift recovers the entire original square-zero shear under identification. -/
theorem nilpotentShearEquiv_eq_squareZero (he : e ^ 2 = 0) (q : R[T;T⁻¹]) :
    (nilpotentShearEquiv t e ⟨2, he⟩ (q.coeff 1)
      (LaurentBoundaryCorrectionSplit.boundaryLift t q)).toAlgHom.toRingHom =
    (squareZeroShear t e het (LaurentBoundaryCorrectionSplit.boundaryLift t q)).toRingHom.comp
      (ringMap (RingHom.id R) ((1 + e * q.coeff 1) * t) t
        (nilpotentShear_parameter_eq t e het (q.coeff 1))) := by
  apply chartRing_ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      AlgHom.commutes, ringMap_scalar,
      RingHom.id_apply]
  · change nilpotentShearEquiv t e ⟨2, he⟩ _ _ (leftCoordinate _) =
      squareZeroShear t e het _ (ringMap (RingHom.id R) ((1 + e * q.coeff 1) * t) t
        (nilpotentShear_parameter_eq t e het _)
        (leftCoordinate ((1 + e * q.coeff 1) * t)))
    rw [nilpotentShearEquiv_left, ringMap_left, squareZeroShear_left]
    ring
  · change nilpotentShearEquiv t e ⟨2, he⟩ _ _ (rightCoordinate _) =
      squareZeroShear t e het _ (ringMap (RingHom.id R) ((1 + e * q.coeff 1) * t) t
        (nilpotentShear_parameter_eq t e het _)
        (rightCoordinate ((1 + e * q.coeff 1) * t)))
    rw [nilpotentShearEquiv_right_fixed t e _ _ _
      (boundaryLift_weighted_right t e het q), ringMap_right, squareZeroShear_right]

end FLT.Mazur.PolygonSmoothing
