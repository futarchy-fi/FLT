/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.FieldTheory.NormalizedTrace

/-! # Nested normalized trace projections in an algebraic field extension -/

@[expose] public noncomputable section
namespace PadicHodgeTheory

/-- Normalize to a larger intermediate field and then a smaller one: this is the direct trace. -/
theorem normalizedTrace_nested_projection (F K : Type*) [Field F] [Field K] [CharZero F]
    [Algebra F K] [Algebra.IsIntegral F K] (E₁ E₂ : IntermediateField F K) (h : E₁ ≤ E₂)
    [Algebra.IsIntegral E₁ K] [Algebra.IsIntegral E₂ K] (x : K) :
    algebraMap E₁ K (Algebra.normalizedTrace E₁ K
      (algebraMap E₂ K (Algebra.normalizedTrace E₂ K x))) =
        algebraMap E₁ K (Algebra.normalizedTrace E₁ K x) := by
  let := (IntermediateField.inclusion h).toRingHom.toAlgebra
  have : IsScalarTower E₁ E₂ K := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.IsIntegral E₁ E₂ :=
    ⟨fun x ↦ (Algebra.IsIntegral.isIntegral (R := F) x).tower_top⟩
  rw [Algebra.normalizedTrace_algebraMap_apply, Algebra.normalizedTrace_trans_apply]

end PadicHodgeTheory
