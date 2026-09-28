/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.Analysis.Normed.Field.CubicHensel
public import FLT.Mathlib.Analysis.Normed.Field.MultivariableNewton
public import FLT.Mathlib.Analysis.Normed.Field.ScalarPerturbation

/-!
# Newton lifting for coupled cubic systems

A system with coordinatewise cubic terms and arbitrary linear coupling admits
a unique nearby root when its inverse Jacobian and the two nonlinear terms
satisfy the indicated bounds. The quadratic remainder retains the factor of
three, as in the one-variable cubic lemma. The number of coordinates is arbitrary.

This is a theorem about the displayed polynomial systems; it does not assert
that every killed-by-three finite flat model has such a presentation.
-/

@[expose] public noncomputable section

open scoped NNReal

namespace IsNonarchimedean
variable {F ι : Type*} [NormedField F] [CompleteSpace F] [Fintype ι]

/-- A coupled cubic system has a unique root in the prescribed ball if
its inverse Jacobian controls the initial error and both nonlinear terms.
The quadratic bound retains the norm of three. -/
theorem existsUnique_root_cubic_system (hna : IsNonarchimedean (norm : F → ℝ))
    (A : (ι → F) →ₗ[F] (ι → F)) (b x : ι → F)
    (J : (ι → F) ≃ₗ[F] (ι → F)) (B : ℝ≥0) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hx : ‖x‖ ≤ 1)
    (hJ : ∀ z i, J z i = 3 * x i ^ 2 * z i + A z i)
    (hJinv : ∀ w, ‖J.symm w‖ ≤ B * ‖w‖)
    (hf : B * ‖fun i ↦ x i ^ 3 + A x i + b i‖ ≤ ρ)
    (hq : B * (‖(3 : F)‖ * ρ) < 1) (hc : B * ρ ^ 2 < 1) :
    ∃! y : ι → F, ‖y - x‖ ≤ ρ ∧ ∀ i, y i ^ 3 + A y i + b i = 0 := by
  let f : (ι → F) → (ι → F) := fun y i ↦ y i ^ 3 + A y i + b i
  let L : ℝ≥0 := ⟨max (‖(3 : F)‖ * ρ) (ρ ^ 2),
    le_max_of_le_right (sq_nonneg ρ)⟩
  have hk : B * L < 1 := by
    change (B : ℝ) * max (‖(3 : F)‖ * ρ) (ρ ^ 2) < 1
    rw [mul_max_of_nonneg _ _ (NNReal.coe_nonneg B)]
    exact max_lt hq hc
  have hrem (z w : ι → F) (hz : ‖z‖ ≤ ρ) (hw : ‖w‖ ≤ ρ) :
      ‖f (x + z) - f (x + w) - J (z - w)‖ ≤ L * ‖z - w‖ := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg L.coe_nonneg (norm_nonneg _))).mpr
    intro i
    have he : (f (x + z) - f (x + w) - J (z - w)) i =
        3 * x i * (z i ^ 2 - w i ^ 2) + (z i ^ 3 - w i ^ 3) := by
      dsimp only [f, Pi.sub_apply]
      rw [hJ]
      simp only [map_add, map_sub, Pi.add_apply, Pi.sub_apply]
      ring
    rw [he]
    have hzi : ‖z i‖ ≤ ρ := (norm_le_pi_norm z i).trans hz
    have hwi : ‖w i‖ ≤ ρ := (norm_le_pi_norm w i).trans hw
    have hxi : ‖x i‖ ≤ 1 := (norm_le_pi_norm x i).trans hx
    have hdiff : ‖z i - w i‖ ≤ ‖z - w‖ := norm_le_pi_norm (z - w) i
    apply (hna _ _).trans
    apply max_le
    · rw [norm_mul, norm_mul]
      calc
        _ ≤ ‖(3 : F)‖ * 1 * (ρ * ‖z i - w i‖) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hxi (norm_nonneg _))
            (hna.norm_sq_sub_sq_le hzi hwi) (norm_nonneg _) (by positivity)
        _ ≤ ‖(3 : F)‖ * 1 * (ρ * ‖z - w‖) := by gcongr
        _ = (‖(3 : F)‖ * ρ) * ‖z - w‖ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    · exact (hna.norm_cube_sub_cube_le hzi hwi).trans
        ((mul_le_mul_of_nonneg_left hdiff (sq_nonneg ρ)).trans
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)))
  obtain ⟨y, hy, huniq⟩ := NonarchimedeanNewton.existsUnique_root_of_linear_remainder_bound
    (hna.norm_pi (ι := ι)) f x J.toAddEquiv B L hρ hJinv hf hk hrem
  refine ⟨y, ⟨hy.1, fun i ↦ congrFun hy.2 i⟩, fun z hz ↦ ?_⟩
  exact huniq z ⟨hz.1, funext hz.2⟩

end IsNonarchimedean
