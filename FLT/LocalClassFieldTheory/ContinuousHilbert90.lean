/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.FieldUnitInvariants
public import FLT.LocalClassFieldTheory.IntegralLowDegreeComparison
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90

/-!
# Continuous Hilbert 90

Finite Hilbert 90 applies to every open normal invariant stage. The proved
continuous cohomology colimit extends it to arbitrary Galois extensions.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open CategoryTheory Limits HomologicalComplex GaloisRepresentation.Extensions

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]

attribute [local instance] fieldUnitAction

/-- Regard an open Galois subgroup as closed, without changing its subgroup. -/
def galoisOpenStageClosed (N : OpenNormalSubgroup Gal(L/K)) : ClosedSubgroup Gal(L/K) :=
  ⟨N.toSubgroup, N.toOpenSubgroup.isClosed⟩

/-- Open Galois subgroups have finite fixed fields. -/
theorem galoisOpenStage_fixedField_finite (N : OpenNormalSubgroup Gal(L/K)) :
    FiniteDimensional K (IntermediateField.fixedField N.toSubgroup) := by
  apply (InfiniteGalois.isOpen_iff_finite _).mp
  change IsOpen (IntermediateField.fixedField
    (galoisOpenStageClosed K L N).toSubgroup).fixingSubgroup.carrier
  rw [InfiniteGalois.fixingSubgroup_fixedField (galoisOpenStageClosed K L N)]
  exact N.isOpen

/-- Each finite invariant stage has trivial first cohomology by finite Hilbert 90. -/
theorem fieldUnitInvariantStageH1_isZero (N : OpenNormalSubgroup Gal(L/K)) :
    IsZero ((invariantStageCohomologyDiagram ℤ Gal(L/K) (Additive Lˣ) 1).obj N) := by
  let NC := galoisOpenStageClosed K L N
  let : NC.Normal := by change N.toSubgroup.Normal; infer_instance
  let := galoisOpenStage_fixedField_finite K L N
  have h : IsZero (groupCohomology
      (Rep.ofAlgebraAutOnUnits K (IntermediateField.fixedField N.toSubgroup)) 1) :=
    ModuleCat.isZero_iff_subsingleton.mpr inferInstance
  exact h.of_iso (fieldUnitInvariantCohomologyIso K L NC 1)

variable [TopologicalSpace (Additive Lˣ)] [DiscreteTopology (Additive Lˣ)]

/-- Continuous multiplicative H1 vanishes for any Galois extension. -/
theorem continuousFieldUnitH1_isZero :
    IsZero (continuousCohomology ℤ Gal(L/K) (Additive Lˣ) 1) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  suffices h : ∀ x : continuousCohomology ℤ Gal(L/K) (Additive Lˣ) 1, x = 0 from
    ⟨fun x y => (h x).trans (h y).symm⟩
  intro x
  obtain ⟨N, y, rfl⟩ := complexCocone_homology_surjective
    (invariantStageDiagram ℤ Gal(L/K) (Additive Lˣ))
    (continuousStageCocone ℤ Gal(L/K) (Additive Lˣ))
    (continuousStageInflation_injective ℤ Gal(L/K) (Additive Lˣ))
    (continuousStageInflation_jointly_surjective ℤ Gal(L/K) (Additive Lˣ)) 1 x
  have hy : y = 0 := (ModuleCat.isZero_iff_subsingleton.mp
    (fieldUnitInvariantStageH1_isZero K L (OrderDual.ofDual N))).elim y 0
  rw [hy, map_zero]
  rfl

/-- Every continuous crossed homomorphism has an actual field-unit witness. -/
theorem continuousFieldUnitCocycle_eq_coboundary
    (c : ContinuousCocycle Gal(L/K) (Additive Lˣ)) :
    ∃ a : Additive Lˣ, ∀ g, c.val g = g • a - a := by
  apply (integralH1Class_eq_zero (k := ℤ) c).mp
  exact (ModuleCat.isZero_iff_subsingleton.mp (continuousFieldUnitH1_isZero K L)).elim _ _

end LocalClassFieldTheory
