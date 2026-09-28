/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FontaineCubicLifting
public import FLT.Mathlib.Analysis.Normed.Field.CubicSystemHensel

/-!
# Integral lifting of coupled cubic systems at the Fontaine radius

Over a finite three-adic extension, a coupled cubic system with inverse
Jacobian bounded by three has a unique integral root near every approximate
root of precision `m > 3/2`. The root retains precision `m - 1`.

The theorem requires the displayed cubic form and the inverse-Jacobian bound.
It does not identify an arbitrary finite flat coordinate algebra with such a
system, nor assume the existence of a compatible root.
-/

@[expose] public noncomputable section

open scoped NNReal

namespace ThreeAdicPlan

variable (E : Type*) [Field E] [Algebra ℚ_[3] E] [Algebra ℤ_[3] E]
  [IsScalarTower ℤ_[3] ℚ_[3] E] [FiniteDimensional ℚ_[3] E]

/-- A coupled cubic system with inverse-Jacobian bound three lifts uniquely
in integral coordinates at precision `m - 1` whenever `m > 3/2`. -/
theorem existsUnique_integral_cubic_system_root {ι : Type*} [Fintype ι]
    (A : (ι → E) →ₗ[E] (ι → E)) (b : ι → E) (x : ι → ThreeAdicIntegers E)
    (J : (ι → E) ≃ₗ[E] (ι → E))
    (hJ : ∀ z i, J z i = 3 * (x i : E) ^ 2 * z i + A z i)
    {m : ℚ} (hm : 3 / 2 < m) :
    letI := spectralNorm.nontriviallyNormedField ℚ_[3] E
    (∀ w, ‖J.symm w‖ ≤ 3 * ‖w‖) →
    (∀ i, ‖(x i : E) ^ 3 + A (fun k ↦ (x k : E)) i + b i‖ ≤
      (3 : ℝ) ^ (-(m : ℝ))) →
    ∃! y : ι → ThreeAdicIntegers E,
      (∀ i, y i - x i ∈ threeAdicValuationIdeal E (m - 1)) ∧
      ∀ i, (y i : E) ^ 3 + A (fun k ↦ (y k : E)) i + b i = 0 := by
  let := spectralNorm.nontriviallyNormedField ℚ_[3] E
  intro hinv hf
  let ρ := (3 : ℝ) ^ (-((m - 1 : ℚ) : ℝ))
  have hρ : 0 ≤ ρ := Real.rpow_nonneg (by norm_num) _
  obtain ⟨hρ1, hρ2⟩ := cubic_hensel_radius_bounds hm
  have hx : ‖fun i ↦ (x i : E)‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
    intro i
    exact (isIntegral_iff_spectralNorm_le_one E _).mp (x i).property
  have hinit : (3 : ℝ≥0) * ‖fun i ↦ (x i : E) ^ 3 +
      A (fun k ↦ (x k : E)) i + b i‖ ≤ ρ := by
    have hb := (pi_norm_le_iff_of_nonneg (Real.rpow_nonneg (by norm_num) _)).mpr hf
    calc
      _ ≤ 3 * (3 : ℝ) ^ (-(m : ℝ)) := mul_le_mul_of_nonneg_left hb (by norm_num)
      _ = (3 : ℝ) ^ (1 + -(m : ℝ)) := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 3), Real.rpow_one]
      _ = ρ := by
        dsimp only [ρ]
        congr 1
        push_cast
        ring
  have h3 : ‖(3 : E)‖ = (3 : ℝ)⁻¹ := spectralNorm_three E
  have hq : (3 : ℝ≥0) * (‖(3 : E)‖ * ρ) < 1 := by
    rw [h3]
    change (3 : ℝ) * ((3 : ℝ)⁻¹ * ρ) < 1
    calc
      _ = ρ := by ring
      _ < 1 := hρ1
  have hc : (3 : ℝ≥0) * ρ ^ 2 < 1 := by
    change (3 : ℝ) * ρ ^ 2 < 1
    calc
      _ < 3 * (3 : ℝ)⁻¹ := mul_lt_mul_of_pos_left hρ2 (by norm_num)
      _ = 1 := by norm_num
  obtain ⟨y, hy, huniq⟩ :=
    (isNonarchimedean_spectralNorm (K := ℚ_[3]) (L := E)).existsUnique_root_cubic_system
      A b (fun i ↦ (x i : E)) J 3 hρ hx hJ hinv hinit hq hc
  have hyint (i : ι) : ‖y i‖ ≤ 1 := by
    have hclose : ‖y i - (x i : E)‖ ≤ ρ := (norm_le_pi_norm _ i).trans hy.1
    have hna := isNonarchimedean_spectralNorm (K := ℚ_[3]) (L := E)
      (y i - (x i : E)) (x i : E)
    rw [sub_add_cancel] at hna
    exact hna.trans (max_le (hclose.trans hρ1.le) ((norm_le_pi_norm _ i).trans hx))
  let yO : ι → ThreeAdicIntegers E := fun i ↦
    ⟨y i, (isIntegral_iff_spectralNorm_le_one E _).mpr (hyint i)⟩
  refine ⟨yO, ⟨fun i ↦ (norm_le_pi_norm _ i).trans hy.1, hy.2⟩, ?_⟩
  intro z hz
  have he : (fun i ↦ (z i : E)) = y := huniq _
    ⟨(pi_norm_le_iff_of_nonneg hρ).mpr hz.1, hz.2⟩
  funext i
  apply Subtype.ext
  exact congrFun he i

end ThreeAdicPlan
