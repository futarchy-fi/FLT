/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.TateCurve.Points

/-!
# Addition for the Tate point map

Periodicity and inversion prove the addition law whenever an argument or its
product lies in `q^ℤ`. The remaining cases require identities between coordinates.
-/

@[expose] public section

open ValuativeRel

namespace TateCurve

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DecidableEq K]

/-- The addition law holds when the first argument is a power of the parameter. -/
theorem uniformizationPoint_mul_of_left_mem (q : Kˣ)
    (hq : valuation K (q : K) < 1) (u v : Kˣ) (hu : u ∈ Subgroup.zpowers q) :
    uniformizationPoint q hq (u * v) =
      uniformizationPoint q hq u + uniformizationPoint q hq v := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  rw [uniformizationPoint_zpow_mul]
  have hz : uniformizationPoint q hq (q ^ m) = 0 :=
    (uniformizationPoint_eq_zero q _ hq).mpr
      (Subgroup.zpow_mem _ (Subgroup.mem_zpowers q) m)
  rw [hz, zero_add]

/-- The addition law holds when the second argument is a power of the parameter. -/
theorem uniformizationPoint_mul_of_right_mem (q : Kˣ)
    (hq : valuation K (q : K) < 1) (u v : Kˣ) (hv : v ∈ Subgroup.zpowers q) :
    uniformizationPoint q hq (u * v) =
      uniformizationPoint q hq u + uniformizationPoint q hq v := by
  rw [mul_comm, uniformizationPoint_mul_of_left_mem q hq v u hv, add_comm]

/-- The addition law holds when the arguments are inverse modulo powers of the parameter. -/
theorem uniformizationPoint_mul_of_mul_mem (q : Kˣ)
    (hq : valuation K (q : K) < 1) (u v : Kˣ) (huv : u * v ∈ Subgroup.zpowers q) :
    uniformizationPoint q hq (u * v) =
      uniformizationPoint q hq u + uniformizationPoint q hq v := by
  have hz : uniformizationPoint q hq (u * v) = 0 :=
    (uniformizationPoint_eq_zero q _ hq).mpr huv
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp huv
  have hv : v = q ^ m * u⁻¹ := by rw [hm]; simp
  rw [hz, hv, uniformizationPoint_zpow_mul, uniformizationPoint_inv, add_neg_cancel]

/-- To prove the full addition law it suffices to treat three nonidentity quotient classes. -/
theorem uniformizationPoint_mul_of_nonexceptional (q : Kˣ)
    (hq : valuation K (q : K) < 1)
    (h : ∀ u v : Kˣ, u ∉ Subgroup.zpowers q → v ∉ Subgroup.zpowers q →
      u * v ∉ Subgroup.zpowers q → uniformizationPoint q hq (u * v) =
        uniformizationPoint q hq u + uniformizationPoint q hq v) (u v : Kˣ) :
    uniformizationPoint q hq (u * v) =
      uniformizationPoint q hq u + uniformizationPoint q hq v := by
  by_cases hu : u ∈ Subgroup.zpowers q
  · exact uniformizationPoint_mul_of_left_mem q hq u v hu
  by_cases hv : v ∈ Subgroup.zpowers q
  · exact uniformizationPoint_mul_of_right_mem q hq u v hv
  by_cases huv : u * v ∈ Subgroup.zpowers q
  · exact uniformizationPoint_mul_of_mul_mem q hq u v huv
  exact h u v hu hv huv

end TateCurve
