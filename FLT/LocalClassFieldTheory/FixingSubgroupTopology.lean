/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.GaloisKernelTopology
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The fixing subgroup as a topological Galois group

The usual fixing-subgroup equivalence is continuous in both directions.
For a finite intermediate field its cosets are finite and count its degree.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

variable (K C : Type) [Field K] [Field C] [Algebra K C] [IsGalois K C]
  (E : IntermediateField K C)

/-- The fixing subgroup is compact in its inherited Krull topology. -/
theorem fixingSubgroupCompact [FiniteDimensional K E] : CompactSpace E.fixingSubgroup :=
  isCompact_iff_compactSpace.mp E.fixingSubgroup_isClosed.isCompact

/-- The inverse fixing-subgroup equivalence is restriction of scalars. -/
theorem fixingSubgroupEquiv_symm_continuous :
    Continuous (IntermediateField.fixingSubgroupEquiv E).symm :=
  (galoisRestrictScalars_continuous K C E).subtype_mk _

/-- Compactness upgrades the algebraic fixing-subgroup equivalence to a homeomorphism. -/
theorem fixingSubgroupEquiv_continuous :
    Continuous (IntermediateField.fixingSubgroupEquiv E) :=
  Continuous.continuous_symm_of_equiv_compact_to_t2
    (f := (IntermediateField.fixingSubgroupEquiv E).symm.toEquiv)
    (fixingSubgroupEquiv_symm_continuous K C E)

variable [FiniteDimensional K E]

/-- A finite intermediate field has finitely many fixing-subgroup cosets. -/
@[instance_reducible] def fixingSubgroupCosetFintype : Fintype (Gal(C/K) ⧸ E.fixingSubgroup) := by
  let : Finite (Gal(C/K) ⧸ E.fixingSubgroup) :=
    E.fixingSubgroup.quotient_finite_of_isOpen E.fixingSubgroup_isOpen
  exact Fintype.ofFinite _

omit [FiniteDimensional K E] in
/-- The coset cardinal is the extension degree, also for nonnormal extensions. -/
theorem fixingSubgroup_card_eq_finrank [Fintype (Gal(C/K) ⧸ E.fixingSubgroup)] :
    Fintype.card (Gal(C/K) ⧸ E.fixingSubgroup) = Module.finrank K E := by
  rw [IntermediateField.finrank_eq_fixingSubgroup_index, Subgroup.index_eq_card,
    Nat.card_eq_fintype_card]

end LocalClassFieldTheory
