/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedUnion

/-!
# Cofinality of the degree-indexed unramified stages

A finite subextension of the union has a primitive element. That element
lies in one finite unramified stage, which therefore contains the entire
subextension.
-/

@[expose] public noncomputable section

universe u

namespace LocalClassFieldTheory

open IsLocalRing

variable (R K C : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  [Algebra.IsSeparable K C] [Finite (ResidueField R)] [IsSepClosed C]
  [IsAdicComplete (maximalIdeal R) R]

/-- Each finite subextension of the unramified union is contained in a finite stage. -/
theorem exists_unramifiedStage_of_finite_le (E : IntermediateField K C)
    [FiniteDimensional K E] (hE : E ≤ maximalUnramified R K C) :
    ∃ n : ℕ+, E ≤ unramifiedStage R K C n := by
  obtain ⟨t, ht⟩ := Field.exists_primitive_element K E
  obtain ⟨n, hn⟩ := (mem_maximalUnramified_iff R K C (t : C)).mp (hE t.property)
  have hgen : IntermediateField.adjoin K {(t : C)} = E := by
    have h := congrArg (fun F : IntermediateField K E => F.map E.val) ht
    simpa only [IntermediateField.coe_val, IntermediateField.adjoin_map, Set.image_singleton,
      ← AlgHom.fieldRange_eq_map, IntermediateField.fieldRange_val] using h
  exact ⟨n, hgen ▸ IntermediateField.adjoin_simple_le_iff.mpr hn⟩

end LocalClassFieldTheory
