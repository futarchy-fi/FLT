/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassRetainedNodeFactorRatioMap

/-!
# The full retained right coordinate is the reciprocal original ratio

The equality keeps the square of the opposite factor, all nilpotent terms,
and the exact normalized smoothing, at arbitrary starting thickness.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (π s c3 c4 c6 : R)
  (I : Ideal R) (hI : IsNilpotent I) (ha : IsUnit W.a₁)
  (hs : s ∈ I) (h2 : W.a₂ ∈ I) (h3 : c3 ∈ I) (h4 : c4 ∈ I) (h6 : c6 ∈ I)
local notation "B" => ChartRing π
local notation "C" => algebraMap R B
local notation "a" => zeroInitialTangentUnit W ha
local notation "U" => retainedOppositeUnit W π s c3 c4 c6 I hI ha hs h2 h3 h4 h6
local notation "E" => retainedRightEvaluation π
local notation "v" => retainedFactorCorrectionUnit W π s c3 c4 c6 I hI ha hs h2 h3 h4 h6
local notation "u" => factorRatioLaurentUnit W ha s (π * c3) (π * c4) (π ^ 2 * c6)
  I hI hs h2 (I.mul_mem_left π h3) (I.mul_mem_left π h4) (I.mul_mem_left (π ^ 2) h6)
attribute [local irreducible] retainedOppositeUnit factorRatioLaurentUnit

/-- The complete corrected right coordinate is exactly the inverse original Laurent unit. -/
theorem retainedFactorCorrection_right :
    E (rightCoordinate π * (v : B)) = (↑(u)⁻¹ : R[T;T⁻¹]) := by
  apply (Units.mul_right_inj u).mp
  rw [Units.mul_inv]
  rw [map_mul, retainedRightEvaluation_right, retainedFactorCorrectionUnit]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_map, map_mul, map_pow]
  rw [factorRatioLaurentUnit_coe,
    ← retainedOppositeFactor_right W π s c3 c4 c6 I hI ha hs h2 h3 h4 h6,
    ← retainedOppositeUnit_val]
  simp only [MonoidHom.coe_ofClass, AlgHom.commutes]
  have ha' : algebraMap R R[T;T⁻¹] (↑a⁻¹ : R) * algebraMap R R[T;T⁻¹] (a : R) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have hu : E (U : B) * E (↑(U)⁻¹ : B) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  calc
    _ = (algebraMap R R[T;T⁻¹] (↑a⁻¹ : R) * algebraMap R R[T;T⁻¹] (a : R)) ^ 2 *
        (LaurentPolynomial.T (-1) * LaurentPolynomial.T 1) *
        (E (U : B) * E (↑(U)⁻¹ : B)) ^ 2 := by ring
    _ = 1 := by rw [ha', hu, ← LaurentPolynomial.T_add]; norm_num

variable (d : R) (hd : s = π * d)
local notation "τ" => initialTangentSmoothing W ha s
local notation "F" => retainedFactorRatioEvaluation W π s c3 c4 c6 I hI ha hs h2 h3 h4 h6 d hd

/-- The entire retained map has the prescribed reciprocal right Laurent coordinate. -/
theorem retainedFactorRatioEvaluation_right_boundary :
    E (F (rightCoordinate τ)) = (↑(u)⁻¹ : R[T;T⁻¹]) := by
  rw [retainedFactorRatioEvaluation_right]
  exact retainedFactorCorrection_right W π s c3 c4 c6 I hI ha hs h2 h3 h4 h6

end FLT.Mazur.WeierstrassModificationX
