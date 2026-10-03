/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.LittleWedderburn
public import Mathlib.RingTheory.SimpleModule.Rank

/-!
# The scalar field of a finite simple module

Schur's lemma and the finite division ring theorem construct the field.
When the original scalar actions commute, its action has rank one.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

variable (A M : Type*) [Ring A] [AddCommGroup M] [Module A M]
  [IsSimpleModule A M] [Finite M]

/-- The actual endomorphism field of a finite simple module. -/
def SimpleScalarField := Module.End A M

instance instFiniteSimpleScalarField : Finite (SimpleScalarField A M) := by
  change Finite (Module.End A M)
  exact Finite.of_injective DFunLike.coe DFunLike.coe_injective

noncomputable instance instFieldSimpleScalarField : Field (SimpleScalarField A M) := by
  classical
  let : Finite (Module.End A M) := instFiniteSimpleScalarField A M
  exact Finite.divisionRing_to_field (Module.End A M)

instance instModuleSimpleScalarField : Module (SimpleScalarField A M) M :=
  Module.End.applyModule

/-- Commuting original scalars act transitively on the nonzero simple module. -/
theorem simpleScalarField_finrank [SMulCommClass A A M] :
    Module.finrank (SimpleScalarField A M) M = 1 := by
  apply isSimpleModule_iff_finrank_eq_one.mp
  apply isSimpleModule_iff_toSpanSingleton_surjective.mpr
  refine ⟨IsSimpleModule.nontrivial A M, fun v hv w ↦ ?_⟩
  obtain ⟨a, ha⟩ := IsSimpleModule.toSpanSingleton_surjective A hv w
  exact ⟨DistribSMul.toLinearMap A M a, ha⟩

end ThreeAdicPlan
