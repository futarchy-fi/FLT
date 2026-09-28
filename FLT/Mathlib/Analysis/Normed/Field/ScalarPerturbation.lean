/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Inverting small perturbations of scalar matrices

Over a nonarchimedean field, a matrix entrywise closer to `a I` than `‖a‖`
is invertible. Its inverse has the exact norm scaling factor `‖a‖⁻¹`.
The estimate has no factor depending on the matrix dimension.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace IsNonarchimedean

variable {F V : Type*} [NormedField F] [NormedAddCommGroup V] [NormedSpace F V]

/-- A linear map closer to scalar multiplication than the scalar norm
has exactly the same norm on every vector as scalar multiplication. -/
theorem norm_eq_of_scalar_perturbation (hna : IsNonarchimedean (norm : V → ℝ))
    (J : V →ₗ[F] V) (a : F) {ε : ℝ} (hε : ε < ‖a‖)
    (hJ : ∀ v, ‖J v - a • v‖ ≤ ε * ‖v‖) (v : V) :
    ‖J v‖ = ‖a‖ * ‖v‖ := by
  by_cases hv : v = 0
  · simp [hv]
  have hlt : ‖J v - a • v‖ < ‖a • v‖ := by
    rw [norm_smul]
    exact (hJ v).trans_lt (mul_lt_mul_of_pos_right hε (norm_pos_iff.mpr hv))
  have he := hna.add_eq_right_of_lt (fun x ↦ norm_neg x) hlt
  simpa only [sub_add_cancel, norm_smul] using he

/-- A small scalar perturbation in finite dimension is invertible, with
an exact norm formula for its inverse. -/
theorem exists_linearEquiv_of_scalar_perturbation [FiniteDimensional F V]
    (hna : IsNonarchimedean (norm : V → ℝ))
    (J : V →ₗ[F] V) (a : F) {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε < ‖a‖)
    (hJ : ∀ v, ‖J v - a • v‖ ≤ ε * ‖v‖) :
    ∃ e : V ≃ₗ[F] V, (∀ v, e v = J v) ∧
      ∀ w, ‖e.symm w‖ = ‖w‖ / ‖a‖ := by
  have ha : ‖a‖ ≠ 0 := ne_of_gt (hε0.trans_lt hε)
  have hinj : Function.Injective J := by
    intro v w hvw
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    have hn := hna.norm_eq_of_scalar_perturbation J a hε hJ (v - w)
    rw [map_sub, hvw, sub_self, norm_zero] at hn
    exact (mul_eq_zero.mp hn.symm).resolve_left ha
  let e := LinearEquiv.ofInjectiveEndo J hinj
  refine ⟨e, fun _ ↦ rfl, fun w ↦ ?_⟩
  have hn := hna.norm_eq_of_scalar_perturbation J a hε hJ (e.symm w)
  have he : J (e.symm w) = w := e.apply_symm_apply w
  rw [he] at hn
  apply (eq_div_iff ha).mpr
  rw [mul_comm, ← hn]

end IsNonarchimedean

namespace Matrix
variable {F ι : Type*} [NormedField F] [Fintype ι]

/-- An entrywise matrix bound controls its action for the supremum norm
without a dimension factor over a nonarchimedean field. -/
theorem norm_mulVec_le_of_entry_bound (hna : IsNonarchimedean (norm : F → ℝ))
    (A : Matrix ι ι F) (c : ℝ) (hc : 0 ≤ c)
    (hA : ∀ i j, ‖A i j‖ ≤ c) (v : ι → F) :
    ‖A *ᵥ v‖ ≤ c * ‖v‖ := by
  classical
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hc (norm_nonneg v))).mpr
  intro i
  change ‖∑ j, A i j * v j‖ ≤ c * ‖v‖
  have hsum (s : Finset ι) : ‖∑ j ∈ s, A i j * v j‖ ≤ c * ‖v‖ := by
    induction s using Finset.induction_on with
    | empty => simpa using mul_nonneg hc (norm_nonneg v)
    | @insert j s hj ih =>
      rw [Finset.sum_insert hj]
      apply (hna _ _).trans
      refine max_le ?_ ih
      rw [norm_mul]
      exact mul_le_mul (hA i j) (norm_le_pi_norm v j) (norm_nonneg _) hc
  exact hsum Finset.univ

end Matrix

namespace IsNonarchimedean
variable {F ι : Type*} [NormedField F] [Fintype ι]

/-- Finite products preserve the nonarchimedean norm inequality. -/
theorem norm_pi (hna : IsNonarchimedean (norm : F → ℝ)) :
    IsNonarchimedean (norm : (ι → F) → ℝ) := by
  intro v w
  apply (pi_norm_le_iff_of_nonneg (le_max_of_le_left (norm_nonneg v))).mpr
  intro i
  exact (hna (v i) (w i)).trans (max_le_max (norm_le_pi_norm v i) (norm_le_pi_norm w i))

end IsNonarchimedean

namespace Matrix
variable {F ι : Type*} [NormedField F] [Fintype ι] [DecidableEq ι]

/-- A matrix congruent to a nonzero scalar matrix up to a strictly smaller
entrywise error defines an equivalence with controlled inverse norm. -/
theorem exists_linearEquiv_of_entrywise_scalar_perturbation
    (hna : IsNonarchimedean (norm : F → ℝ))
    (A : Matrix ι ι F) (a : F) {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε < ‖a‖)
    (hA : ∀ i j, ‖A i j - (if i = j then a else 0)‖ ≤ ε) :
    ∃ e : (ι → F) ≃ₗ[F] (ι → F), (∀ v, e v = A *ᵥ v) ∧
      ∀ w, ‖e.symm w‖ = ‖w‖ / ‖a‖ := by
  apply hna.norm_pi.exists_linearEquiv_of_scalar_perturbation A.mulVecLin a hε0 hε
  intro v
  have hentries : ∀ i j, ‖(A - a • (1 : Matrix ι ι F)) i j‖ ≤ ε := by
    intro i j
    simpa [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] using hA i j
  have hh := norm_mulVec_le_of_entry_bound hna (A - a • (1 : Matrix ι ι F)) ε hε0 hentries v
  simpa only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    Matrix.mulVecLin_apply] using hh

end Matrix
