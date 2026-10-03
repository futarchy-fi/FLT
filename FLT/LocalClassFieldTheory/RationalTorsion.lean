/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.Topology.Instances.AddCircle.Defs
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic

/-!
# Rational torsion coordinates for local invariants

The map from Z/n to Q/Z sends the residue of j to j/n, with positive sign.
Its image is exactly the n-torsion subgroup. This constructs the coefficient
coordinates, not an invariant on local Galois cohomology.
-/

@[expose] public section

namespace LocalClassFieldTheory

variable (n : ℕ) [NeZero n]

/-- Positive rational coordinates on the n-torsion of Q/Z. -/
noncomputable def zmodToRatCircle : ZMod n →+ AddCircle (1 : ℚ) :=
  ZMod.lift n ⟨AddMonoidHom.mk' (fun j ↦ ↑((j : ℚ) / n)) (by simp [add_div]),
    by simp [NeZero.ne n]⟩

/-- The coordinate of an integer residue is the positive fraction j/n. -/
@[simp] theorem zmodToRatCircle_intCast (j : ℤ) :
    zmodToRatCircle n (j : ZMod n) = (↑((j : ℚ) / n) : AddCircle (1 : ℚ)) := by
  simp [zmodToRatCircle]

/-- Formula using the canonical representative in [0,n). -/
theorem zmodToRatCircle_apply (j : ZMod n) :
    zmodToRatCircle n j = (↑((j.val : ℚ) / n) : AddCircle (1 : ℚ)) := by
  simpa using zmodToRatCircle_intCast n (j.val : ℤ)

/-- Distinct residues give distinct rational torsion coordinates. -/
theorem zmodToRatCircle_injective : Function.Injective (zmodToRatCircle n) := by
  intro x y hxy
  have hn : (0 : ℚ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  rwa [zmodToRatCircle_apply, zmodToRatCircle_apply,
    AddCircle.coe_eq_coe_iff_of_mem_Ico, div_left_inj' hn.ne', Nat.cast_inj,
    (ZMod.val_injective n).eq_iff] at hxy <;>
    exact ⟨by positivity, by simpa only [zero_add, div_lt_one hn, Nat.cast_lt]
      using (ZMod.val_lt _)⟩

/-- The rational torsion coordinate detects zero. -/
@[simp] theorem zmodToRatCircle_eq_zero (j : ZMod n) :
    zmodToRatCircle n j = 0 ↔ j = 0 :=
  map_eq_zero_iff _ (zmodToRatCircle_injective n)

/-- Every coordinate is killed by n. -/
theorem nsmul_zmodToRatCircle (j : ZMod n) : n • zmodToRatCircle n j = 0 := by
  rw [← map_nsmul]
  simp [nsmul_eq_mul]

/-- Every n-torsion rational class has a unique residue coordinate. -/
theorem mem_range_zmodToRatCircle (x : AddCircle (1 : ℚ)) :
    x ∈ (zmodToRatCircle n).range ↔ n • x = 0 := by
  constructor
  · rintro ⟨j, rfl⟩
    exact nsmul_zmodToRatCircle n j
  · induction x using Quotient.inductionOn with | h q =>
      intro hq
      rw [← AddCircle.coe_nsmul, AddCircle.coe_eq_zero_iff] at hq
      obtain ⟨j, hj⟩ := hq
      have hn : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
      have hjq : (j : ℚ) / n = q := by
        simpa [zsmul_eq_mul, nsmul_eq_mul, mul_comm] using
          (div_eq_iff hn).mpr (by simpa [zsmul_eq_mul, nsmul_eq_mul, mul_comm] using hj)
      exact ⟨(j : ZMod n), by rw [zmodToRatCircle_intCast, hjq]⟩

end LocalClassFieldTheory
