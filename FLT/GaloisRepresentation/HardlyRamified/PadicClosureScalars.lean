/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicIntegers

/-! # Continuous integral scalars on the p-adic algebraic closure -/

@[expose] public noncomputable section
namespace PadicAlgCl
variable (p : ℕ) [Fact p.Prime]

/-- The canonical integral scalar map is continuous through its fraction field. -/
theorem continuous_padicInt_algebraMap :
    Continuous (algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p])) := by
  rw [IsScalarTower.algebraMap_eq ℤ_[p] ℚ_[p] (AlgebraicClosure ℚ_[p]), RingHom.coe_comp]
  exact (continuous_algebraMap ℚ_[p] _).comp continuous_subtype_val

/-- Joint continuity of the canonical integral action. -/
instance continuousSMulPadicInt : ContinuousSMul ℤ_[p] (AlgebraicClosure ℚ_[p]) :=
  continuousSMul_of_algebraMap ℤ_[p] _ (continuous_padicInt_algebraMap p)

end PadicAlgCl
