/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Normalized order on the multiplicative group of a local field

Negating the exponent of the normalized multiplicative valuation gives the
classical integer order. Its kernel is the actual valuation-ring unit group.
-/

@[expose] public section

namespace LocalClassFieldTheory

open ValuativeRel IsNonarchimedeanLocalField
open scoped WithZero

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]

/-- Classical normalized order, encoded as a multiplicative homomorphism. -/
noncomputable def normalizedOrder : Kˣ →* Multiplicative ℤ where
  toFun u := Multiplicative.ofAdd
    (-WithZero.log (valueGroupWithZeroIsoInt K (valuation K (u : K))))
  map_one' := by simp
  map_mul' u v := by
    have hu : valueGroupWithZeroIsoInt K (valuation K (u : K)) ≠ 0 := by simp
    have hv : valueGroupWithZeroIsoInt K (valuation K (v : K)) ≠ 0 := by simp
    simp [Units.val_mul, map_mul, WithZero.log_mul hu hv, mul_comm]

/-- Recover the multiplicative valuation from the integer order. -/
theorem normalizedOrder_exp (u : Kˣ) :
    WithZero.exp (-(normalizedOrder K u).toAdd) =
      valueGroupWithZeroIsoInt K (valuation K (u : K)) := by
  change WithZero.exp (- -WithZero.log _) = _
  rw [neg_neg, WithZero.exp_log (by simp)]

/-- Order zero means valuation one, with no choice of a uniformizer. -/
theorem normalizedOrder_eq_one_iff (u : Kˣ) :
    normalizedOrder K u = 1 ↔ valuation K (u : K) = 1 := by
  constructor
  · intro hu
    have h := normalizedOrder_exp K u
    rw [hu] at h
    have he : valueGroupWithZeroIsoInt K (valuation K (u : K)) = 1 := by
      simpa using h.symm
    exact (map_eq_one_iff _ (valueGroupWithZeroIsoInt K).injective).mp he
  · intro hu
    simp [normalizedOrder, hu]

/-- The kernel is the unit subgroup of the valuation ring, not an assumed subgroup. -/
theorem normalizedOrder_ker :
    (normalizedOrder K).ker = (valuation K).valuationSubring.unitGroup := by
  ext u
  exact (normalizedOrder_eq_one_iff K u).trans
    (Valuation.mem_unitGroup_iff K (valuation K) u).symm

/-- Every integer occurs as the normalized order of a nonzero field element. -/
theorem normalizedOrder_surjective : Function.Surjective (normalizedOrder K) := by
  intro m
  obtain ⟨x, hx⟩ := valuation_surjective ((valueGroupWithZeroIsoInt K).symm
    (WithZero.exp (-m.toAdd)))
  have hx0 : x ≠ 0 := by
    intro h
    have he := congrArg (valueGroupWithZeroIsoInt K) hx
    simpa [h] using he.symm
  refine ⟨Units.mk0 x hx0, ?_⟩
  simp [normalizedOrder, hx]

/-- An element of order one chosen from the proved surjectivity. -/
noncomputable def orderOneUnit : Kˣ :=
  (normalizedOrder_surjective K (Multiplicative.ofAdd 1)).choose

/-- The chosen element has positive classical order one. -/
@[simp] theorem normalizedOrder_orderOneUnit :
    normalizedOrder K (orderOneUnit K) = Multiplicative.ofAdd 1 :=
  (normalizedOrder_surjective K (Multiplicative.ofAdd 1)).choose_spec

/-- Order one corresponds to exponent minus one for Mathlib's multiplicative valuation. -/
theorem value_orderOneUnit :
    valueGroupWithZeroIsoInt K (valuation K (orderOneUnit K : K)) = WithZero.exp (-1 : ℤ) := by
  simpa using (normalizedOrder_exp K (orderOneUnit K)).symm

/-- Valuation-ring units have order zero. -/
@[simp] theorem normalizedOrder_unit (u : (valuation K).valuationSubringˣ) :
    normalizedOrder K (Units.map (valuation K).valuationSubring.subtype u) = 1 := by
  apply (normalizedOrder_eq_one_iff K _).mpr
  apply (Valuation.mem_unitGroup_iff K (valuation K) _).mp
  exact ((valuation K).valuationSubring.unitGroupMulEquiv.symm u).property

end LocalClassFieldTheory
