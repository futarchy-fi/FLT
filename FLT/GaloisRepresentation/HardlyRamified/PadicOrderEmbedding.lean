/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.Defs
public import FLT.GaloisRepresentation.HardlyRamified.PadicClosureScalars

/-! # A continuous embedding of the original coefficient order into the algebraic closure -/

@[expose] public noncomputable section
namespace PadicOrderEmbedding
variable (p : ℕ) [Fact p.Prime] (R : Type*) [CommRing R] [IsDomain R]
  [Algebra ℤ_[p] R] [Module.Free ℤ_[p] R] [Module.Finite ℤ_[p] R]

/-- Embed the actual coefficient order, preserving its p-adic scalar map. -/
def embedding : R →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p] := by
  letI : Module.IsTorsionFree ℤ_[p] (AlgebraicClosure ℚ_[p]) :=
    Module.IsTorsionFree.trans ℚ_[p]
  exact IsAlgClosed.lift

/-- The chosen coefficient embedding as an algebra structure. -/
@[instance_reducible] def algebra : Algebra R (AlgebraicClosure ℚ_[p]) :=
  (embedding p R).toRingHom.toAlgebra

theorem scalarTower : letI := algebra p R; IsScalarTower ℤ_[p] R (AlgebraicClosure ℚ_[p]) := by
  let := algebra p R
  exact IsScalarTower.of_algebraMap_eq (R := ℤ_[p]) (S := R) (A := AlgebraicClosure ℚ_[p])
    fun x ↦ ((embedding p R).commutes x).symm

variable [TopologicalSpace R] [IsTopologicalRing R] [IsModuleTopology ℤ_[p] R]

omit [IsTopologicalRing R] in
/-- Finite-module topology makes the actual embedding continuous. -/
theorem continuous_embedding : Continuous (embedding p R) :=
  IsModuleTopology.continuous_of_linearMap (embedding p R).toLinearMap

omit [IsTopologicalRing R] in
theorem continuousSMul : letI := algebra p R; ContinuousSMul R (AlgebraicClosure ℚ_[p]) := by
  let := algebra p R
  exact continuousSMul_of_algebraMap R _ (continuous_embedding p R)

end PadicOrderEmbedding
