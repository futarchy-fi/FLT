/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedStageTower

/-!
# The union of the finite unramified stages

The directed supremum is a Galois intermediate field. Its elements lie in
finite unramified stages, and it contains every finite unramified stage.
No topological inverse-limit or inertia comparison is asserted here.
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

/-- The maximal unramified extension, as the supremum of its constructed finite stages. -/
def maximalUnramified : IntermediateField K C := ⨆ n : ℕ+, unramifiedStage R K C n

/-- Each finite stage embeds by inclusion into the supremum. -/
theorem unramifiedStage_le_maximalUnramified (n : ℕ+) :
    unramifiedStage R K C n ≤ maximalUnramified R K C := le_iSup _ n

/-- Every element of the supremum already lies in one finite unramified stage. -/
theorem mem_maximalUnramified_iff (x : C) :
    x ∈ maximalUnramified R K C ↔ ∃ n : ℕ+, x ∈ unramifiedStage R K C n := by
  change x ∈ (↑(⨆ n : ℕ+, unramifiedStage R K C n) : Set C) ↔ _
  rw [IntermediateField.coe_iSup_of_directed (unramifiedStage_directed R K C), Set.mem_iUnion]
  rfl

/-- The union contains every actual finite unramified intermediate field. -/
theorem IsUnramifiedStage.le_maximalUnramified {E : IntermediateField K C}
    (hE : IsUnramifiedStage R K E) : E ≤ maximalUnramified R K C := by
  obtain ⟨n, rfl⟩ := hE.eq_unramifiedStage R K C
  exact unramifiedStage_le_maximalUnramified R K C n

/-- Normality passes from the constructed stages to their supremum. -/
theorem maximalUnramified_normal : Normal K (maximalUnramified R K C) := by
  let : ∀ n : ℕ+, Normal K (unramifiedStage R K C n) :=
    fun n => (unramifiedStage_isUnramified R K C n).normal
  exact IntermediateField.normal_iSup K C _

/-- The union is a Galois extension of the base field. -/
theorem maximalUnramified_isGalois : IsGalois K (maximalUnramified R K C) := by
  let := maximalUnramified_normal R K C
  exact ⟨⟩

end LocalClassFieldTheory
