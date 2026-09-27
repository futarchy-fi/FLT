/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Tactic.Ring

/-! # Fixed vectors for the weak Chebotarev argument

In dimension two, the trace identity `tr A = 1 + det A` characterizes the
existence of a nonzero fixed vector. This property survives taking powers
and conjugating a representation element.

These are leaves C1 and C2 of `docs/CHEBOTAREV_PLAN.md`. The transport lemma
does not need the plan's finite-dimensional hypothesis.
-/

@[expose] public section

namespace GaloisRepresentation.B5Inputs

/-- In dimension two, the trace identity is equivalent to a nonzero fixed vector. -/
theorem trace_eq_one_add_det_iff_fixedVector
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (hV : Module.finrank k V = 2) (A : Module.End k V) :
    A.trace k V = 1 + A.det ↔ ∃ v : V, v ≠ 0 ∧ A v = v := by
  have hdet : (A - 1).det = 1 + A.det - A.trace k V := by
    let b := Module.finBasisOfFinrankEq k V hV
    rw [LinearMap.trace_eq_matrix_trace k b, ← LinearMap.det_toMatrix b A,
      ← LinearMap.det_toMatrix b, map_sub, LinearMap.toMatrix_one]
    simp only [Matrix.det_fin_two, Matrix.trace, Matrix.diag, Fin.sum_univ_two,
      Matrix.sub_apply, Matrix.one_apply, Fin.isValue, Fin.zero_eq_one_iff,
      Fin.one_eq_zero_iff, Nat.reduceEqDiff, ↓reduceIte]
    ring
  have hsing : A.trace k V = 1 + A.det ↔ (A - 1).det = 0 := by
    rw [hdet, sub_eq_zero, eq_comm]
  rw [hsing, LinearMap.det_eq_zero_iff_ker_ne_bot, Submodule.ne_bot_iff]
  simp only [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
  exact exists_congr fun v => and_comm

/-- A nonzero fixed vector gives one for every conjugate of a nonnegative power. -/
theorem fixedVector_conj_pow
    {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (a t : G) (n : ℕ)
    (h : ∃ v : V, v ≠ 0 ∧ ρ a v = v) :
    ∃ w : V, w ≠ 0 ∧ ρ (t * a ^ n * t⁻¹) w = w := by
  obtain ⟨v, hv, ha⟩ := h
  have hpow : ρ (a ^ n) v = v := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, map_mul, Module.End.mul_apply, ha, ih]
  refine ⟨ρ t v, ?_, ?_⟩
  · intro hzero
    apply hv
    have hinv := congrArg (ρ t⁻¹) hzero
    simpa using hinv
  · simp only [map_mul, Module.End.mul_apply, ρ.inv_self_apply, hpow]

end GaloisRepresentation.B5Inputs
