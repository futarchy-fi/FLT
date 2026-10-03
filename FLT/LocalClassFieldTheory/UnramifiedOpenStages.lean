/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedStageOrderH2

/-!
# Constructed stages refine every open subgroup

The fixing groups of degree-indexed stages are open and normal. They form a
cofinal family for the open-normal-subgroup cohomology diagram.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing
open scoped Topology

variable (R K C : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  [Algebra.IsSeparable K C] [Finite (ResidueField R)] [IsSepClosed C]
  [IsAdicComplete (maximalIdeal R) R]

local notation "U" => maximalUnramified R K C

local instance unramifiedUnionGalois : IsGalois K U := maximalUnramified_isGalois R K C

/-- The fixing group of a constructed finite stage, with its actual open normal structure. -/
def unramifiedOpenStage (n : UnramifiedIndex) : OpenNormalSubgroup Gal(U/K) where
  toSubgroup := (unramifiedFiniteStage R K C n).toIntermediateField.fixingSubgroup
  isOpen' := IntermediateField.fixingSubgroup_isOpen _

/-- Every open subgroup contains one of the constructed finite-stage fixing groups. -/
theorem exists_unramifiedOpenStage_le (N : OpenNormalSubgroup Gal(U/K)) :
    ∃ n, unramifiedOpenStage R K C n ≤ N := by
  obtain ⟨E, hE, hEN⟩ := (krullTopology_mem_nhds_one_iff K U _).mp
    (N.isOpen.mem_nhds N.one_mem)
  let := hE
  let := (IntermediateField.liftAlgEquiv E).toLinearEquiv.finiteDimensional
  obtain ⟨n, hn⟩ := exists_unramifiedStage_of_finite_le R K C
    (IntermediateField.lift E) (IntermediateField.lift_le E)
  have hET : E ≤ (unramifiedFiniteStage R K C ⟨n⟩).toIntermediateField := by
    intro x hx
    exact (mem_unramifiedFiniteStage R K C ⟨n⟩ x).mpr
      (hn ((IntermediateField.mem_lift x).mpr hx))
  exact ⟨⟨n⟩, fun _ hg => hEN (E.fixingSubgroup_le hET hg)⟩

end LocalClassFieldTheory
