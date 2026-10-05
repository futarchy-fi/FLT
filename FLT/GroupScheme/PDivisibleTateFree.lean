/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleTateFinite
public import Mathlib.LinearAlgebra.FreeModule.PID

/-! # Torsion-freeness and finite freeness of the original Tate module -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem R K p height)

/-- A coherent Tate vector killed by p is zero, using the actual closed inclusions. -/
theorem tateSequences_eq_zero_of_prime_smul (x : X.tateSequences)
    (hx : (p : ℤ_[p]) • x = 0) : x = 0 := by
  apply X.tate_ext
  intro n
  apply X.inclusion_points_injective (Nat.le_succ n)
  rw [map_zero, ← X.tateEval_reduction (Nat.le_succ n) x, ← genericHom_comp,
    X.reduction_inclusion, FF.genericHom_multiply]
  have he : (p : ℤ_[p]) • X.tateEvalLinear (n + 1) x = 0 := by
    rw [← map_smul, hx, map_zero]
  change (p : ℤ_[p]) • X.tateEval (n + 1) x = 0 at he
  simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel_left, pow_one, map_zero,
    Nat.cast_smul_eq_nsmul] using he

/-- The actual inverse limit has no torsion over the p-adic integers. -/
theorem tateSequences_isTorsionFree : Module.IsTorsionFree ℤ_[p] X.tateSequences := by
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro a x hx
  by_cases ha : a = 0
  · exact Or.inl ha
  right
  obtain ⟨n, u, rfl⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha PadicInt.irreducible_p
  have hpow : (p : ℤ_[p]) ^ n • x = 0 := by
    apply u.isUnit.smul_left_cancel.mp
    simpa only [mul_smul, smul_zero] using hx
  clear hx ha u
  induction n with
  | zero => simpa using hpow
  | succ n ih =>
    apply ih
    apply X.tateSequences_eq_zero_of_prime_smul
    simpa only [pow_succ', mul_smul] using hpow

/-- Finite generation and torsion-freeness make the original Tate module free. -/
theorem tateSequences_free : Module.Free ℤ_[p] X.tateSequences := by
  let : Module.Finite ℤ_[p] X.tateSequences := X.tateSequences_finite
  let : Module.IsTorsionFree ℤ_[p] X.tateSequences := X.tateSequences_isTorsionFree
  infer_instance
end ThreeAdicPlan.PDivisibleSystem
