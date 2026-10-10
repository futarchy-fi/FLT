/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Flatness from regularity of the power-series parameter

Over a field every nonzero power series is a power of the parameter times a
unit. Parameter regularity therefore implies torsion-freeness, hence flatness
over the power-series discrete valuation ring.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.PowerSeriesParameterFlatness

variable (K : Type*) [Field K] (M : Type*) [AddCommGroup M] [Module (PowerSeries K) M]
  (hX : ∀ x : M, (PowerSeries.X : PowerSeries K) • x = 0 → x = 0)

include hX in
/-- Regularity of the parameter gives regularity of every parameter power. -/
theorem pow_smul_eq_zero (d : ℕ) (x : M)
    (hx : (PowerSeries.X : PowerSeries K) ^ d • x = 0) : x = 0 := by
  induction d with
  | zero => simpa only [pow_zero, one_smul] using hx
  | succ d ih =>
    rw [pow_succ', mul_smul] at hx
    exact ih (hX _ hx)

include hX in
/-- A module with regular parameter has no torsion under any nonzero power series. -/
theorem isTorsionFree : Module.IsTorsionFree (PowerSeries K) M := by
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro f x hx
  by_cases hf : f = 0
  · exact Or.inl hf
  right
  rw [← PowerSeries.X_pow_order_mul_divXPowOrder (f := f), mul_smul] at hx
  have hu := pow_smul_eq_zero K M hX _ _ hx
  exact (PowerSeries.isUnit_divided_by_X_pow_order hf).smul_eq_zero.mp hu

include hX in
/-- Parameter regularity suffices for flatness over the complete coefficient ring. -/
theorem flat : Module.Flat (PowerSeries K) M := by
  let _ := isTorsionFree K M hX
  infer_instance

end FLT.Mazur.PowerSeriesParameterFlatness
