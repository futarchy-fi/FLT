/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentPairNaturality

/-!
# Coefficients after evaluation at a scaled Laurent coordinate

Substituting a times the Laurent coordinate preserves each exponent and
multiplies its coefficient by the corresponding integral power of a.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.LaurentScaledEvaluationCoefficients
open LaurentPolynomial PolygonChartScaling PolygonScalingNaturality
variable {R S : Type*} [CommRing R] [CommRing S]

/-- The unit Laurent coordinate raised to any integral power is the corresponding monomial. -/
theorem coordinate_one_zpow (d : ℤ) :
    ((coordinateUnit (1 : Sˣ)) ^ d).val = (T d : S[T;T⁻¹]) := by
  have he := congrArg (fun f : S[T;T⁻¹] →+* S[T;T⁻¹] ↦ f (T d))
    (laurent_one (R := S))
  simpa only [laurent, eval₂_T, RingHom.id_apply] using he

/-- A scaled coordinate is the constant unit times the unscaled coordinate. -/
theorem coordinate_factor (u : Sˣ) : coordinateUnit u =
    Units.map (C : S →+* S[T;T⁻¹]) u * coordinateUnit (1 : Sˣ) := by
  apply Units.ext
  simp [coordinateUnit]

/-- Scaling the unit coordinate scales every Laurent monomial by the corresponding unit power. -/
theorem coordinate_zpow (u : Sˣ) (d : ℤ) :
    (coordinateUnit u ^ d).val = C (u ^ d).val * T d := by
  rw [coordinate_factor, mul_zpow, Units.val_mul, coordinate_one_zpow]
  congr 1
  exact congrArg Units.val
    (map_zpow (Units.map (C : S →+* S[T;T⁻¹]).toMonoidHom) u d).symm

/-- Evaluation at a scaled coordinate has a coefficientwise formula at every integer exponent. -/
theorem eval₂_scaled_coeff (f : R →+* S) (u : Sˣ) (p : R[T;T⁻¹]) (d : ℤ) :
    (eval₂ (C.comp f) (coordinateUnit u) p).coeff d = f (p.coeff d) * (u ^ d).val := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, add_mul, hp, hq]
  | C_mul_T k a =>
    rw [map_mul, eval₂_C, eval₂_T, coordinate_zpow, RingHom.comp_apply,
      ← mul_assoc, ← map_mul]
    simp only [← smul_eq_C_mul, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul, T_apply]
    split_ifs with hk
    · subst k
      simp
    · simp

end FLT.Mazur.LaurentScaledEvaluationCoefficients
