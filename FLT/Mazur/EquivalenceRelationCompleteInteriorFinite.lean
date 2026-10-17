/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationCompleteTestFinite
public import FLT.Mazur.EquivalenceRelationFiniteCompleteInterior
public import FLT.Mazur.SchemeFiniteTargetFppfBaseChange

/-!
# Complete interiors detect exactly the original finite target locus

Finiteness of the whole pullback descends along the etale frame map. Thus an
interior complete frame forces an actual finite neighborhood of the original
projection. Complete closed tests alone do not have this consequence.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) [LocallyQuasiFinite p]
  (I : Type) [Fintype I] (o : I)
attribute [local irreducible] source first completeInterior

include e in
/-- Flat locally presented complete tests force actual original finite target neighborhoods. -/
theorem complete_flat_test_range_le_finiteTarget {T : Scheme} (j : T ⟶ source p q I o)
    [Flat j] [LocallyOfFinitePresentation j]
    (hj : Set.range j ⊆ completePointLocus (p := p) (q := q) I o) :
    Set.range (j ≫ first p q I o) ⊆ finiteTargetOpen p := by
  let _ := first_etale e I o
  let _ := original_pullback_finite_of_complete I o j hj
  rintro _ ⟨x, rfl⟩
  apply (mem_finiteTargetOpen_fppf_iff
    (IsPullback.of_hasPullback p (j ≫ first p q I o)) x).mp
  rw [finiteTargetOpen_eq_top]
  trivial

include e in
/-- A complete interior point lies above the exact finite locus of the original projection. -/
theorem completeInterior_le_finiteTarget :
    completeInterior (p := p) (q := q) I o ≤ first p q I o ⁻¹ᵁ finiteTargetOpen p := by
  intro x hx
  exact complete_flat_test_range_le_finiteTarget e I o (completeInterior I o).ι
    (fun _ ⟨y, hy⟩ ↦ hy ▸ completeInterior_subset I o y.property)
    ⟨⟨x, hx⟩, rfl⟩

include e in
/-- Interior completeness is exactly completeness together with original local finiteness. -/
theorem mem_completeInterior_iff_finiteTarget (x : source p q I o) :
    x ∈ completeInterior (p := p) (q := q) I o ↔
      x ∈ completePointLocus (p := p) (q := q) I o ∧
        first p q I o x ∈ finiteTargetOpen p :=
  ⟨fun hx ↦ ⟨completeInterior_subset I o hx, completeInterior_le_finiteTarget e I o hx⟩,
    fun hx ↦ complete_mem_interior_of_finiteTarget I o x hx.1 hx.2⟩

variable [QuasiCompact p]

include e in
/-- The complete-interior route covers precisely the original finite target locus. -/
theorem finiteTarget_iff_exists_completeInterior (x : A) :
    x ∈ finiteTargetOpen p ↔
      ∃ (n : ℕ) (o : Fin n) (y : source p q (Fin n) o),
        first p q (Fin n) o y = x ∧ y ∈ completeInterior (Fin n) o := by
  constructor
  · exact exists_complete_interior_lift_of_finiteTarget e x
  · rintro ⟨n, o, y, hy, hc⟩
    exact hy ▸ completeInterior_le_finiteTarget e (Fin n) o hc

end FLT.Mazur.EquivalenceRelationNormalizedFrames
