/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.DvrAdicTopology
public import FLT.LocalClassFieldTheory.NormalLatticePower
public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Openness of the constructed integral normal lattice

A nonzero scalar multiple of the open ring of integers lies in the lattice.
It is a neighborhood of zero, so the lattice is open in the actual topology
induced by the maximal-ideal valuation on the fraction field.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open scoped nonZeroDivisors

variable (R S K L : Type)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [IsScalarTower R S L]
  [FiniteDimensional K L] [IsGalois K L]

omit [FaithfulSMul R S] in
/-- The normal lattice is open for the actual local-field valuation topology. -/
theorem integralNormalLattice_isOpen :
    letI := dvrAdicValued S L
    IsOpen (integralNormalLattice R K L : Set L) := by
  let := dvrAdicValued S L
  obtain ⟨d, hd, hdx⟩ := integralNormalLattice_common_denominator R S K L
  have hdL : algebraMap R L d ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply R K L]
    simpa using (algebraMap K L).injective.ne ((IsFractionRing.injective R K).ne hd)
  let U := (fun x : L => algebraMap R L d * x) '' Set.range (algebraMap S L)
  have hU : IsOpen U :=
    (Homeomorph.mulLeft₀ (algebraMap R L d) hdL).isOpenMap _ (dvrAdicValued_integers_isOpen S L)
  have h0 : (0 : L) ∈ U := ⟨0, ⟨0, map_zero _⟩, mul_zero _⟩
  apply (integralNormalLattice R K L).toAddSubgroup.isOpen_of_mem_nhds
  apply Filter.mem_of_superset (hU.mem_nhds h0)
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  change algebraMap R L d * algebraMap S L x ∈ integralNormalLattice R K L
  simpa only [Algebra.smul_def] using hdx x

end LocalClassFieldTheory
