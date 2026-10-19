/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeFrameCompletenessTransfer

/-!
# A missing original section of an incomplete geometric frame

Over a separably closed field, failure to enumerate the whole original fiber
constructs an actual section outside every displayed coordinate. The section
uses the same field and the same endpoint as the original frame.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme} (E : Over S) [Etale E.hom] [IsSeparated E.hom]
  (I : Type) [Fintype I] {K : Type} [Field K] [IsSepClosed K]
  {b : Spec (.of K) ⟶ S} (t : Over.mk b ⟶ distinctScheme E I)

/-- Incompleteness constructs a section of the full original fiber over the unchanged field. -/
theorem exists_missing_geometric_section
    (ht : ¬ Function.Bijective (fun i ↦ geometricCoordinate E I t i default)) :
    ∃ a : Spec (.of K) ⟶ pullback E.hom b,
      a ≫ pullback.snd E.hom b = 𝟙 _ ∧
      ∀ i, a default ≠ geometricCoordinate E I t i default := by
  have hn : ¬ Function.Surjective (fun i ↦ geometricCoordinate E I t i default) :=
    fun h ↦ ht ⟨geometricCoordinate_point_injective E I t, h⟩
  unfold Function.Surjective at hn
  push Not at hn
  obtain ⟨x, hx⟩ := hn
  obtain ⟨a, ha⟩ := EtaleGeometricSections.evaluation_surjective (pullback.snd E.hom b) x
  refine ⟨a.val, a.property, fun i h ↦ hx i ?_⟩
  exact h.symm.trans ha

/-- The missing section gives an actual original arrow, distinct from all frame coordinates. -/
theorem exists_missing_original_section
    (ht : ¬ Function.Bijective (fun i ↦ geometricCoordinate E I t i default)) :
    ∃ a : Over.mk b ⟶ E, ∀ i, a ≠ t ≫ distinctCoordinate E I i := by
  obtain ⟨a, ha, hne⟩ := exists_missing_geometric_section E I t ht
  let r : Over.mk b ⟶ E := Over.homMk (a ≫ pullback.fst E.hom b) (by
    change (a ≫ pullback.fst E.hom b) ≫ E.hom = b
    rw [Category.assoc, pullback.condition, ← Category.assoc, ha, Category.id_comp])
  refine ⟨r, fun i hi ↦ hne i ?_⟩
  apply congrArg (fun z : Spec (.of K) ⟶ pullback E.hom b ↦ z default)
  apply pullback.hom_ext
  · exact (congrArg Over.Hom.left hi).trans (geometricCoordinate_fst E I t i).symm
  · rw [ha, geometricCoordinate_snd]

end FLT.Mazur.RelativeOrderedTuples
