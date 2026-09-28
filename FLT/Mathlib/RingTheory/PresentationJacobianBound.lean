/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.GeneratorsDifferentialRelations
public import Mathlib.RingTheory.Extension.Presentation.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Jacobian determinant bounds for generating square presentations

If `a` kills the differentials of an algebra presented by `n` generators and
`n` relations, the Jacobian determinant divides `a ^ n` in the algebra.
Unlike selecting `n` elements of the relation ideal, this calculation uses
that the given relations generate the entire ideal. Existence of a square
presentation is not asserted here.
-/

@[expose] public noncomputable section

open MvPolynomial

namespace Algebra.Presentation

variable {R S ι σ : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The evaluated gradient of every relation is a linear combination of the
evaluated gradients of the defining relations. -/
theorem exists_coefficients_pderiv [Fintype σ] (P : Presentation R S ι σ)
    {f : MvPolynomial ι R} (hf : f ∈ P.ker) :
    ∃ c : σ → S, ∀ j,
      aeval P.val (pderiv j f) = ∑ i, c i * aeval P.val (pderiv j (P.relation i)) := by
  classical
  rw [← P.span_range_relation_eq_ker] at hf
  obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp hf
  refine ⟨fun i ↦ aeval P.val (c i), fun j ↦ ?_⟩
  simp only [map_sum, pderiv_mul, map_add, map_mul, P.aeval_val_relation,
    mul_zero, zero_add]

/-- Differential annihilation gives a left multiplier taking the full
Jacobian matrix of a square presentation to the scalar matrix. -/
theorem exists_mul_jacobian_eq_scalar [Fintype ι] [DecidableEq ι]
    (P : Presentation R S ι ι) (a : R)
    (ha : ∀ ω : KaehlerDifferential R S, a • ω = 0) :
    ∃ Q : Matrix ι ι S,
      Q * Matrix.of (fun i j ↦ aeval P.val (pderiv j (P.relation i))) =
        algebraMap R S a • (1 : Matrix ι ι S) := by
  choose f hf hdf using P.toGenerators.exists_relation_pderiv_eq a ha
  choose c hc using fun i ↦ P.exists_coefficients_pderiv (hf i)
  refine ⟨Matrix.of c, ?_⟩
  ext i j
  rw [Matrix.mul_apply]
  change (∑ k, c i k * aeval P.val (pderiv j (P.relation k))) = _
  rw [← hc i j, hdf i j]
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]

/-- In a genuine square presentation with `n` variables, the Jacobian
determinant divides the `n`-th power of every differential annihilator.
At integral points this gives the valuation bound `v(det J) ≤ n * v(a)`. -/
theorem jacobian_det_dvd_pow [Fintype ι] [DecidableEq ι]
    (P : Presentation R S ι ι) (a : R)
    (ha : ∀ ω : KaehlerDifferential R S, a • ω = 0) :
    Matrix.det (fun i j ↦ aeval P.val (pderiv j (P.relation i))) ∣
      (algebraMap R S a) ^ Fintype.card ι := by
  obtain ⟨Q, hQ⟩ := P.exists_mul_jacobian_eq_scalar a ha
  have h := congrArg Matrix.det hQ
  rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one] at h
  exact ⟨Q.det, by rw [mul_comm]; exact h.symm⟩

end Algebra.Presentation
