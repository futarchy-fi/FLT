/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassChartEvaluationComparison
public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point

/-!
# Normalized projective points and integral chart evaluations

Normalized coordinates identify actual chart points with projective classes.
For nonzero discriminant every normalized solution is nonsingular, and every
nonsingular projective point has such a normalized representative.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassCurve.Projective

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {K : Type u} [Field K]

/-- Normalized vectors represent the same projective class exactly when their ratios agree. -/
theorem normalized_projective_eq_iff (j k : Fin 3) (v w : Fin 3 → K)
    (hj : v j = 1) (hk : w k = 1) :
    (⟦v⟧ : PointClass K) = ⟦w⟧ ↔ ∀ i, v i = v k * w i := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := Quotient.exact h
    have hka : v k = (a : K) := by
      rw [← ha]
      simp [hk, Units.smul_def, smul_eq_mul]
    intro i
    rw [hka, ← ha]
    rfl
  · intro h
    have hn : v k ≠ 0 := by
      intro hz
      have he := h j
      rw [hj, hz, zero_mul] at he
      exact one_ne_zero he
    apply Quotient.sound
    refine ⟨Units.mk0 (v k) hn, ?_⟩
    funext i
    exact (h i).symm

/-- A nonzero discriminant makes every normalized solution nonsingular. -/
theorem normalized_equation_nonsingular (W : WeierstrassCurve K) (hΔ : W.Δ ≠ 0)
    (j : Fin 3) (v : Fin 3 → K) (hv : W.toProjective.Equation v) (hj : v j = 1) :
    W.toProjective.Nonsingular v := by
  by_cases hz : v 2 = 0
  · have hx := X_eq_zero_of_Z_eq_zero hv hz
    have hy : v 1 ≠ 0 := by
      intro hy
      fin_cases j <;> simp_all
    apply (nonsingular_of_Z_eq_zero hz).mpr
    refine ⟨hv, Or.inr ?_⟩
    simpa only [hx, mul_zero, zero_mul, add_zero, zero_pow two_ne_zero, sub_zero] using
      pow_ne_zero 2 hy
  · apply (nonsingular_of_Z_ne_zero hz).mpr
    apply (W.toAffine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp
    exact (equation_of_Z_ne_zero hz).mp hv

/-- Every nonsingular projective point admits a normalized homogeneous representative. -/
theorem exists_normalized_projective (W : WeierstrassCurve K) (P : W.toProjective.Point) :
    ∃ (j : Fin 3) (v : Fin 3 → K) (_hv : W.toProjective.Equation v) (_hj : v j = 1),
      (⟦v⟧ : PointClass K) = P.point := by
  obtain ⟨v, hv⟩ := Quotient.exists_rep P.point
  have hn : W.toProjective.Nonsingular v := by
    have h := P.nonsingular
    rw [← hv] at h
    exact h
  have he : ∃ j : Fin 3, v j ≠ 0 := by
    by_cases hz : v 2 = 0
    · exact ⟨1, Y_ne_zero_of_Z_eq_zero hn hz⟩
    · exact ⟨2, hz⟩
  obtain ⟨j, hj⟩ := he
  let w := (v j)⁻¹ • v
  have hw : W.toProjective.Equation w :=
    (equation_smul v (isUnit_iff_ne_zero.mpr (inv_ne_zero hj))).mpr hn.left
  refine ⟨j, w, hw, ?_, ?_⟩
  · exact inv_mul_cancel₀ hj
  · exact (smul_eq v (isUnit_iff_ne_zero.mpr (inv_ne_zero hj))).trans hv

variable {R : Type u} [CommRing R] [Algebra R K] (W : WeierstrassCurve R)

/-- Equality of field-valued chart points is equality of the projective classes. -/
theorem integralChartPoint_eq_iff_projective (j k : Fin 3) (v w : Fin 3 → K)
    (hv : (W.map (algebraMap R K)).toProjective.Equation v) (hj : v j = 1)
    (hw : (W.map (algebraMap R K)).toProjective.Equation w) (hk : w k = 1) :
    integralChartPoint W j v hv hj = integralChartPoint W k w hw hk ↔
      (⟦v⟧ : PointClass K) = ⟦w⟧ :=
  (integralChartPoint_eq_iff W j k v w hv hj hw hk).trans
    (normalized_projective_eq_iff j k v w hj hk).symm

end FLT.Mazur.WeierstrassIntegralChart
