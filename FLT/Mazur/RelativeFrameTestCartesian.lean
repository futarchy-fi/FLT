/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeFrameTestSections

/-!
# Cartesian comparison of arbitrary frames with the universal original frame

The full original pullback and every coordinate section commute with arbitrary
scheme-valued tests. These squares retain all residue and nilpotent coefficients.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme.{0}} (E : Over S) [Etale E.hom] [IsSeparated E.hom]
  (I : Type) [Fintype I] {T : Scheme} {b : T ⟶ S}
  (t : Over.mk b ⟶ distinctScheme E I)

/-- Map the whole original scheme-valued fiber to the universal framed source. -/
def testToFramed : pullback E.hom b ⟶ framedSource E I :=
  pullback.lift (pullback.fst E.hom b) (pullback.snd E.hom b ≫ t.left)
    (by rw [Category.assoc, t.w]; exact pullback.condition)

omit [Etale E.hom] in
@[reassoc] theorem testToFramed_fst :
    testToFramed E I t ≫ pullback.fst E.hom (distinctScheme E I).hom =
      pullback.fst E.hom b := pullback.lift_fst _ _ _

omit [Etale E.hom] in
@[reassoc] theorem testToFramed_projection :
    testToFramed E I t ≫ framedProjection E I = pullback.snd E.hom b ≫ t.left :=
  pullback.lift_snd _ _ _

omit [Etale E.hom] in
/-- The entire original scheme-valued fiber is the actual fiber of the framed projection. -/
theorem testToFramed_isPullback :
    IsPullback (testToFramed E I t) (pullback.snd E.hom b)
      (framedProjection E I) t.left := by
  apply IsPullback.of_right (h₁₂ := pullback.fst E.hom (distinctScheme E I).hom)
    (h₂₂ := (distinctScheme E I).hom)
  · rw [testToFramed_fst, t.w]
    exact IsPullback.of_hasPullback E.hom b
  · exact testToFramed_projection E I t
  · exact IsPullback.of_hasPullback E.hom (distinctScheme E I).hom

omit [Etale E.hom] in
/-- Each original scheme-valued coordinate is the pullback of its universal section. -/
@[reassoc] theorem testToFramed_coordinate (i : I) :
    testSection E I t i ≫ testToFramed E I t = t.left ≫ framedSection E I i := by
  apply pullback.hom_ext
  · simp only [Category.assoc, testToFramed_fst, framedSection_original,
      testSection_fst]
    rfl
  · change _ ≫ framedProjection E I = _ ≫ framedProjection E I
    simp only [Category.assoc, testToFramed_projection, testSection_snd_assoc,
      framedSection_projection, Category.comp_id]

omit [Etale E.hom] in
/-- The coordinate comparison is cartesian, including its scheme structure. -/
theorem testToFramed_coordinate_isPullback (i : I) :
    IsPullback t.left (testSection E I t i) (framedSection E I i)
      (testToFramed E I t) := by
  apply IsPullback.of_bot (v₂₁ := pullback.snd E.hom b) (v₂₂ := framedProjection E I)
  · simp only [testSection_snd, framedSection_projection]
    exact IsPullback.of_id_snd
  · exact (testToFramed_coordinate E I t i).symm
  · exact testToFramed_isPullback E I t

end FLT.Mazur.RelativeOrderedTuples
