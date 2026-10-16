/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeCompleteGeometricTuple
public import FLT.Mazur.EtaleGeometricSectionPoints

/-!
# Comparing complete frames on the original geometric test

Completeness of a geometric frame enumerates every original section, not
merely every chosen representative of a fiber point. Consequently any two
complete frames have a unique permutation matching all original arrows.
This statement concerns the full original fiber on the specified test.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme} (E : Over S) [Etale E.hom] [IsSeparated E.hom]
  (I : Type) [Fintype I] {K : Type} [Field K] {b : Spec (.of K) ⟶ S}
  (a : Over.mk b ⟶ distinctScheme E I)
  (ha : Function.Bijective (fun i ↦ geometricCoordinate E I a i default))

include ha in
/-- A complete geometric frame contains every original section over the given endpoint. -/
theorem complete_coordinate_surjective :
    Function.Surjective (fun i ↦ a ≫ distinctCoordinate E I i) := by
  intro r
  let s : Spec (.of K) ⟶ pullback E.hom b :=
    pullback.lift r.left (𝟙 _) (by rw [Category.id_comp]; exact r.w)
  have hs : s ≫ pullback.snd E.hom b = 𝟙 _ := pullback.lift_snd _ _ _
  obtain ⟨i, hi⟩ := ha.2 (s default)
  have he : geometricCoordinate E I a i = s := congrArg Subtype.val
    (EtaleGeometricSections.section_ext (pullback.snd E.hom b)
      (s := ⟨geometricCoordinate E I a i, geometricCoordinate_snd E I a i⟩)
      (t := ⟨s, hs⟩) hi)
  refine ⟨i, Over.OverMorphism.ext ?_⟩
  have h := congrArg (fun z ↦ z ≫ pullback.fst E.hom b) he
  simpa only [geometricCoordinate_fst, s, pullback.lift_fst] using h

include ha in
/-- Completeness gives a bijection with all original sections, without a finite-branch choice. -/
theorem complete_coordinate_bijective :
    Function.Bijective (fun i ↦ a ≫ distinctCoordinate E I i) := by
  let _ : Nonempty (Over.mk b).left := inferInstanceAs (Nonempty (Spec (.of K)))
  exact ⟨distinctCoordinate_injective E I a, complete_coordinate_surjective E I a ha⟩

/-- The entire original section type, enumerated by the given complete frame. -/
def completeCoordinateEquiv : I ≃ (Over.mk b ⟶ E) :=
  Equiv.ofBijective _ (complete_coordinate_bijective E I a ha)

variable (a' : Over.mk b ⟶ distinctScheme E I)
  (ha' : Function.Bijective (fun i ↦ geometricCoordinate E I a' i default))

/-- The unique relabeling matching every original arrow in two complete geometric frames. -/
def completeFrameRelabel : Equiv.Perm I :=
  (completeCoordinateEquiv E I a ha).trans (completeCoordinateEquiv E I a' ha').symm

/-- The relabeling matches the original full relation coordinates, not just their endpoints. -/
theorem completeFrameRelabel_coordinate (i : I) :
    a ≫ distinctCoordinate E I (completeFrameRelabel E I a ha a' ha' |>.symm i) =
      a' ≫ distinctCoordinate E I i := by
  change completeCoordinateEquiv E I a ha
    ((completeCoordinateEquiv E I a ha).symm (completeCoordinateEquiv E I a' ha' i)) = _
  exact (completeCoordinateEquiv E I a ha).apply_symm_apply _

/-- The constructed original permutation takes one complete geometric frame to the other. -/
theorem completeFrameRelabel_action :
    a.left ≫ (distinctAction E I (completeFrameRelabel E I a ha a' ha')).hom = a'.left := by
  let e := completeFrameRelabel E I a ha a' ha'
  let z : Over.mk b ⟶ distinctScheme E I :=
    Over.homMk (a.left ≫ (distinctAction E I e).hom) (by
      rw [Category.assoc, distinctAction_base]; exact a.w)
  have hz : z = a' := by
    apply distinct_hom_ext E I
    intro i
    apply Over.OverMorphism.ext
    change (a.left ≫ (distinctAction E I e).hom) ≫ (distinctCoordinate E I i).left = _
    rw [Category.assoc, distinctAction_coordinate]
    exact congrArg Over.Hom.left (completeFrameRelabel_coordinate E I a ha a' ha' i)
  exact congrArg Over.Hom.left hz

/-- No other permutation identifies these two actual original frames. -/
theorem completeFrameRelabel_unique (e : Equiv.Perm I)
    (he : a.left ≫ (distinctAction E I e).hom = a'.left) :
    e = completeFrameRelabel E I a ha a' ha' := by
  let _ : Nonempty (Over.mk b).left := inferInstanceAs (Nonempty (Spec (.of K)))
  have hsymm : e.symm = (completeFrameRelabel E I a ha a' ha').symm := by
    apply Equiv.ext
    intro i
    apply distinctCoordinate_injective E I a
    apply Over.OverMorphism.ext
    have h := congrArg (fun z ↦ z ≫ (distinctCoordinate E I i).left) he
    rw [Category.assoc, distinctAction_coordinate] at h
    exact h.trans (congrArg Over.Hom.left
      (completeFrameRelabel_coordinate E I a ha a' ha' i)).symm
  exact congrArg Equiv.symm hsymm

end FLT.Mazur.RelativeOrderedTuples
