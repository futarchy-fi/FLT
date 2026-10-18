/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticCyclicState

/-!
# Nilpotence of the actual compatible cyclic smoothings

Compatibility transports the order-zero vanishing through the exact quotient
kernel. Thus every full smoothing is divisible by the original parameter.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.PolygonArithmeticCyclic
open PolygonArithmeticStages
variable {R : Type*} [CommRing R] {π : R} {ι : Type*}
  (S : State R π ι) (hS : S.Compatible)

include hS in
/-- The full scalar smoothing follows every original nonconsecutive quotient. -/
theorem State.parameter_restrictionLE {k m : ℕ} (h : k ≤ m) (i : ι) :
    restrictionLE R π h (S.parameter m i) = S.parameter k i := by
  induction m, h using Nat.le_induction with
  | base => rw [restrictionLE_refl]; rfl
  | succ m h ih =>
    rw [restrictionLE_succ R π h, AlgHom.comp_apply, hS.1 m i, ih]

/-- Top-power annihilation at order zero forces the actual residue smoothing to vanish. -/
theorem State.parameter_zero (ha : S.Annihilated) (i : ι) : S.parameter 0 i = 0 := by
  simpa only [pow_zero, one_mul] using ha 0 i

include hS in
/-- The exact smoothing at every order is divisible by the original parameter. -/
theorem State.parameter_dvd (ha : S.Annihilated) (m : ℕ) (i : ι) :
    PolygonArithmeticStages.parameter R π m ∣ S.parameter m i := by
  have hz := (S.parameter_restrictionLE hS (Nat.zero_le m) i).trans
    (S.parameter_zero ha i)
  simpa only [Nat.zero_add, pow_one] using
    (restrictionLE_eq_zero_iff R π (Nat.zero_le m) (S.parameter m i)).mp hz

include hS in
/-- Every whole node has a nilpotent smoothing, including all accumulated scalar drifts. -/
theorem State.parameter_isNilpotent (ha : S.Annihilated) (m : ℕ) (i : ι) :
    IsNilpotent (S.parameter m i) := by
  obtain ⟨a, he⟩ := S.parameter_dvd hS ha m i
  refine ⟨m + 1, ?_⟩
  rw [he, mul_pow, parameter_pow, zero_mul]

end FLT.Mazur.PolygonArithmeticCyclic
