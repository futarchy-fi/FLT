/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationNormalizedScalarComplete
public import FLT.Mazur.EquivalenceRelationNormalizedActionComplete

/-!
# Intrinsic complete points of the original normalized source

Completeness depends only on the underlying source point, independently of its
field-valued representative. The locus is invariant under the whole original
relation. No openness of this locus is asserted.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)

/-- The intrinsic set of points whose entire original fiber is enumerated by their frame. -/
def completePointLocus : Set (source p q I o) :=
  {x | Complete I o ((source p q I o).fromSpecResidueField x)}

/-- Completeness is independent of the field chosen to represent a source point. -/
theorem complete_iff_mem_completePointLocus {K : Type} [Field K]
    (u : Spec (.of K) ⟶ source p q I o) :
    Complete I o u ↔ u default ∈ completePointLocus (p := p) (q := q) I o := by
  have h := complete_scalar_iff I o
    ((source p q I o).fromSpecResidueField (u (closedPoint K)))
    (Spec.map (Scheme.descResidueField (Scheme.stalkClosedPointTo u)))
  rw [Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField] at h
  change Complete I o u ↔ Complete I o ((source p q I o).fromSpecResidueField (u default))
  exact h.trans (congrArg (fun x ↦ Complete I o ((source p q I o).fromSpecResidueField x))
    (congrArg u (Subsingleton.elim (α := Spec (.of K)) (closedPoint K) default))).to_iff

/-- Any two field-valued representatives of the same source point have the same completeness. -/
theorem complete_iff_of_same_point {K L : Type} [Field K] [Field L]
    (u : Spec (.of K) ⟶ source p q I o) (v : Spec (.of L) ⟶ source p q I o)
    (h : u default = v default) : Complete I o u ↔ Complete I o v := by
  rw [complete_iff_mem_completePointLocus, complete_iff_mem_completePointLocus, h]

include e in
/-- Completeness at either independent endpoint of an original arrow is equivalent. -/
theorem original_arrow_complete_iff {K : Type} [Field K]
    (u v : Spec (.of K) ⟶ source p q I o) (a : Spec (.of K) ⟶ D)
    (ha : a ≫ p = u ≫ first p q I o) (hb : a ≫ q = v ≫ first p q I o) :
    Complete I o u ↔ Complete I o v := by
  refine ⟨complete_of_original_arrow e I o u v a ha hb, ?_⟩
  exact complete_of_original_arrow e I o v u (a ≫ e.s)
    (by rw [Category.assoc, e.symmetry₁]; exact hb)
    (by rw [Category.assoc, e.symmetry₂]; exact ha)

include e in
/-- The intrinsic complete locus is saturated for the entire original relation. -/
theorem completePointLocus_relation_invariant :
    relationFirst p q I o ⁻¹' completePointLocus (p := p) (q := q) I o =
      relationSecond p q I o ⁻¹' completePointLocus (p := p) (q := q) I o := by
  ext x
  let z := (fullRelation p q I o).fromSpecResidueField x
  have h := original_arrow_complete_iff e I o
    (z ≫ relationFirst p q I o) (z ≫ relationSecond p q I o)
    (z ≫ relationArrow p q I o)
    (by simp only [Category.assoc, relationArrow_first])
    (by simp only [Category.assoc, relationArrow_second])
  rw [complete_iff_mem_completePointLocus, complete_iff_mem_completePointLocus] at h
  have hx : z default = x := Scheme.fromSpecResidueField_apply x default
  exact (congrArg (fun y ↦ relationFirst p q I o y ∈
    completePointLocus (p := p) (q := q) I o) hx).to_iff.symm.trans
      (h.trans (congrArg (fun y ↦ relationSecond p q I o y ∈
        completePointLocus (p := p) (q := q) I o) hx).to_iff)

/-- The intrinsic locus is stable under the moving normalized action. -/
theorem completePointLocus_action_invariant (σ : Equiv.Perm I) :
    (action e I o σ).hom ⁻¹' completePointLocus (p := p) (q := q) I o =
      completePointLocus (p := p) (q := q) I o := by
  ext x
  have h := action_complete_iff e I o ((source p q I o).fromSpecResidueField x) σ
  rw [complete_iff_mem_completePointLocus, complete_iff_mem_completePointLocus] at h
  have hx : (source p q I o).fromSpecResidueField x default = x :=
    Scheme.fromSpecResidueField_apply x default
  exact (congrArg (fun y ↦ (action e I o σ).hom y ∈
    completePointLocus (p := p) (q := q) I o) hx).to_iff.symm.trans
      (h.trans (congrArg (fun y ↦ y ∈ completePointLocus (p := p) (q := q) I o) hx).to_iff)

end FLT.Mazur.EquivalenceRelationNormalizedFrames
