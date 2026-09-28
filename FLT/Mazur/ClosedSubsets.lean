/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FCurveContracts

/-!
# Proper closed subsets of an irreducible curve

In an irreducible space of topological Krull dimension at most one, every proper
irreducible closed subset is minimal among irreducible closed subsets. In a T0 space,
such a minimal subset is a singleton. Noetherianity then expresses any proper closed
subset as a finite union of these singletons, including the empty union.

This proves contract C8, leaf FC13 of `docs/FCURVE_CONTRACTS.md`. The argument uses
only T0 separation; neither sobriety nor closedness of every ambient point is required.
-/

@[expose] public section

open Set TopologicalSpace

universe u

namespace FLT.Mazur.FCurve

variable {X : Type u} [TopologicalSpace X]

/-- A proper irreducible closed subset of an irreducible space of dimension at most
one is minimal among irreducible closed subsets. -/
theorem isMin_irreducibleCloseds_of_ne_univ [IrreducibleSpace X]
    (hdim : topologicalKrullDim X ≤ 1) (C : IrreducibleCloseds X)
    (hC : (C : Set X) ≠ univ) : IsMin C := by
  rcases Order.krullDim_le_one_iff.mp hdim C with hmin | hmax
  · exact hmin
  · let U : IrreducibleCloseds X := ⟨univ, IrreducibleSpace.isIrreducible_univ X,
      isClosed_univ⟩
    exact (hC (Set.Subset.antisymm (subset_univ _) (hmax (show C ≤ U from
      subset_univ _)))).elim

/-- Minimal irreducible closed subsets of a T0 space are singletons. -/
theorem eq_singleton_of_isMin_irreducibleCloseds [T0Space X]
    (C : IrreducibleCloseds X) (hC : IsMin C) : ∃ x : X, (C : Set X) = {x} := by
  apply minimal_nonempty_closed_eq_singleton C.isClosed C.isIrreducible.nonempty
  intro T hTC hTne hT
  obtain ⟨x, hx⟩ := hTne
  let D : IrreducibleCloseds X :=
    ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hDT : (D : Set X) ⊆ T := closure_minimal (singleton_subset_iff.mpr hx) hT
  have hCD : (C : Set X) ⊆ D := hC (show D ≤ C from hDT.trans hTC)
  exact hTC.antisymm (hCD.trans hDT)

/-- Every proper irreducible closed subset of an irreducible T0 space of dimension
at most one consists of a single point. -/
theorem eq_singleton_of_isClosed_of_isIrreducible [T0Space X] [IrreducibleSpace X]
    (hdim : topologicalKrullDim X ≤ 1) {C : Set X} (hclosed : IsClosed C)
    (hirr : IsIrreducible C) (hproper : C ≠ univ) : ∃ x : X, C = {x} := by
  let D : IrreducibleCloseds X := ⟨C, hirr, hclosed⟩
  exact eq_singleton_of_isMin_irreducibleCloseds D
    (isMin_irreducibleCloseds_of_ne_univ hdim D hproper)

/-- A proper closed subset of an irreducible Noetherian T0 space of dimension at
most one is finite. The finite decomposition also covers the empty subset. -/
theorem finite_of_isClosed_of_ne_univ [NoetherianSpace X] [T0Space X]
    [IrreducibleSpace X] (hdim : topologicalKrullDim X ≤ 1) {Z : Set X}
    (hclosed : IsClosed Z) (hproper : Z ≠ univ) : Z.Finite := by
  obtain ⟨S, hSfin, hSclosed, hSirr, hZS⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible hclosed
  rw [hZS]
  apply hSfin.sUnion
  intro C hCS
  have hCZ : C ⊆ Z := hZS ▸ subset_sUnion_of_mem hCS
  have hCproper : C ≠ univ := by
    intro hC
    exact hproper (Set.Subset.antisymm (subset_univ _) (hC ▸ hCZ))
  obtain ⟨x, rfl⟩ := eq_singleton_of_isClosed_of_isIrreducible hdim
    (hSclosed C hCS) (hSirr C hCS) hCproper
  exact finite_singleton x

/-- The C8 proper-closed-subset contract. -/
theorem properClosedSubsetFinite (X : Type u) [TopologicalSpace X] :
    ProperClosedSubsetFinite X := by
  intro hnoeth hT0 hirr hdim Z hclosed hproper
  exact finite_of_isClosed_of_ne_univ hdim hclosed hproper

end FLT.Mazur.FCurve
