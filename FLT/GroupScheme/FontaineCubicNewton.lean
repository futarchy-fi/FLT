/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FontaineNewtonStep
public import FLT.GroupScheme.FiniteFlatDifferentials

/-!
# The sharper cubic Newton step

For a presentation `X³ + aX + b`, the quadratic Taylor coefficient at an
integral point is divisible by three. After a Newton correction of precision
`m - 1`, the new error has precision at least `min (2m - 1) (3m - 3)`.
This strictly improves the error precisely in the range relevant to Fontaine,
`m > 3/2`. No cubic presentation is asserted for an arbitrary finite flat model.
-/

@[expose] public noncomputable section

open Polynomial

namespace ThreeAdicPlan

variable (E : Type*) [Field E] [Algebra ℚ_[3] E] [Algebra ℤ_[3] E]
  [IsScalarTower ℤ_[3] ℚ_[3] E] [FiniteDimensional ℚ_[3] E]

/-- The cubic Taylor error retains a factor of three in its quadratic term. -/
theorem cubic_newton_step_mem_valuationIdeal (a b : ℤ_[3])
    (x δ : ThreeAdicIntegers E) {t : ℚ}
    (hδ : δ ∈ threeAdicValuationIdeal E t)
    (hlin : aeval x (X ^ 3 + C a * X + C b) +
      aeval x (X ^ 3 + C a * X + C b).derivative * δ = 0) :
    aeval (x + δ) (X ^ 3 + C a * X + C b) ∈
      threeAdicValuationIdeal E (min (1 + 2 * t) (3 * t)) := by
  have hres : aeval (x + δ) (X ^ 3 + C a * X + C b) =
      3 * x * δ ^ 2 + δ ^ 3 := by
    simp only [derivative_X_pow, derivative_mul, derivative_C,
      derivative_X, zero_mul, mul_one, zero_add, add_zero, map_add, map_mul,
      map_pow, aeval_X, aeval_C] at hlin ⊢
    norm_num at hlin
    erw [map_ofNat] at hlin
    linear_combination hlin
  have hδ2 : δ ^ 2 ∈ threeAdicValuationIdeal E (2 * t) := by
    simpa only [pow_two, two_mul] using mul_mem_threeAdicValuationIdeal E hδ hδ
  have hδ3 : δ ^ 3 ∈ threeAdicValuationIdeal E (3 * t) := by
    rw [show 3 * t = 2 * t + t by ring, show δ ^ 3 = δ ^ 2 * δ by ring]
    exact mul_mem_threeAdicValuationIdeal E hδ2 hδ
  have h3 : (3 : ThreeAdicIntegers E) ∈ threeAdicValuationIdeal E 1 := by
    simpa only [pow_one] using (three_pow_mem_threeAdicValuationIdeal E 1 1).mpr le_rfl
  have hquad : 3 * x * δ ^ 2 ∈ threeAdicValuationIdeal E (1 + 2 * t) := by
    have h := Ideal.mul_mem_left _ x (mul_mem_threeAdicValuationIdeal E h3 hδ2)
    convert h using 1
    ring
  rw [hres]
  exact Ideal.add_mem _
    (threeAdicValuationIdeal_antitone E (min_le_left _ _) hquad)
    (threeAdicValuationIdeal_antitone E (min_le_right _ _) hδ3)

/-- A monogenic killed-by-three algebra with a depressed cubic presentation
admits an integral Newton step at every precision above three halves. -/
theorem _root_.PowerBasis.exists_cubic_newton_step_of_three_smul
    {A : Type*} [CommRing A] [Algebra ℤ_[3] A] (pb : PowerBasis ℤ_[3] A)
    (hΩ : ∀ ω : KaehlerDifferential ℤ_[3] A, (3 : ℤ_[3]) • ω = 0)
    (a b : ℤ_[3]) (hf : minpoly ℤ_[3] pb.gen = X ^ 3 + C a * X + C b)
    (x : ThreeAdicIntegers E) {m : ℚ} (hm : 3 / 2 < m)
    (hx : aeval x (minpoly ℤ_[3] pb.gen) ∈ threeAdicValuationIdeal E m) :
    ∃ y : ThreeAdicIntegers E,
      y - x ∈ threeAdicValuationIdeal E (m - 1) ∧
      aeval y (minpoly ℤ_[3] pb.gen) ∈
        threeAdicValuationIdeal E (min (2 * m - 1) (3 * m - 3)) := by
  have hm1 : 1 < m := by linarith
  obtain ⟨δ, hδ, hlin⟩ := exists_integral_newton_correction E _ x hm1 hx
    (pb.spectralNorm_derivative_ge_of_three_smul E hΩ x hm1 hx)
  refine ⟨x + δ, by simpa only [add_sub_cancel_left] using hδ, ?_⟩
  rw [hf] at hlin ⊢
  convert cubic_newton_step_mem_valuationIdeal E a b x δ hδ hlin using 1
  congr 2 <;> ring

/-- Both cubic error exponents strictly improve the original precision. -/
theorem lt_cubic_newton_precision {m : ℚ} (hm : 3 / 2 < m) :
    m < min (2 * m - 1) (3 * m - 3) := by
  apply lt_min <;> linarith

/-- Specialization of the cubic Newton step to a finite flat model killed by three. -/
theorem FF.exists_cubic_newton_step (M : FF ℤ_[3] ℚ_[3]) (hM : KilledBy 3 M)
    (pb : PowerBasis ℤ_[3] M.CoordinateRing) (a b : ℤ_[3])
    (hf : minpoly ℤ_[3] pb.gen = X ^ 3 + C a * X + C b)
    (x : ThreeAdicIntegers E) {m : ℚ} (hm : 3 / 2 < m)
    (hx : aeval x (minpoly ℤ_[3] pb.gen) ∈ threeAdicValuationIdeal E m) :
    ∃ y : ThreeAdicIntegers E,
      y - x ∈ threeAdicValuationIdeal E (m - 1) ∧
      aeval y (minpoly ℤ_[3] pb.gen) ∈
        threeAdicValuationIdeal E (min (2 * m - 1) (3 * m - 3)) :=
  pb.exists_cubic_newton_step_of_three_smul E (M.three_smul_kaehlerDifferential_eq_zero hM)
    a b hf x hm hx

end ThreeAdicPlan
