/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AuxiliaryLevelFaithfulRepresentation
public import FLT.Mazur.GroupMarkingBaseChange
public import FLT.Mazur.UniversallyDistinctSections

/-!
# Faithful parameters give distinct sections on the actual pulled-back group

The faithful open supplies universal distinctness after arbitrary scheme base
change. Projection retains the original marking, including on nonreduced tests.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.AuxiliaryLevel
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E : Over S) [GrpObj E] [IsSeparated E.hom]
  (A : Type) [Group A] [Fintype A] {T : Scheme} (g : T ⟶ S)
  (f : Over.mk g ⟶ faithfulScheme E A)

/-- The original faithful parameter as sections of the actual base-changed group. -/
def faithfulSectionMarking : A →* (𝟙_ (Over T) ⟶ (Over.pullback g).obj E) :=
  GroupMarkingBaseChange.marking g E (𝟙_ (Over T))
    (markingOf E A
      ((Over.homMk (𝟙 T) (by simp) : (Over.map g).obj (𝟙_ (Over T)) ⟶ Over.mk g) ≫
        f ≫ faithfulInclusion E A))

/-- Every pulled-back section projects to its unchanged original label. -/
@[reassoc] theorem faithfulSectionMarking_fst (a : A) :
    (faithfulSectionMarking E A g f a).left ≫ pullback.fst E.hom g =
      f.left ≫ (faithfulInclusion E A).left ≫ (value E A a).left := by
  rw [faithfulSectionMarking, GroupMarkingBaseChange.marking_fst]
  change ((𝟙 T ≫ f.left) ≫ (faithfulInclusion E A).left) ≫ _ = _
  rw [Category.id_comp, Category.assoc]
  rfl

/-- Faithfulness holds on every nonempty test of the original parameter base. -/
theorem faithfulSectionMarking_distinct :
    UniversallyDistinctSections.UniversallyDistinct (fun a ↦
      faithfulSectionMarking E A g f a) := by
  intro V k hV a b hab
  let _ : Nonempty ((Over.map g).obj V).left := hV
  let j : (Over.map g).obj V ⟶ Over.mk g :=
    Over.homMk k.left (by simpa using congrArg (· ≫ g) k.w)
  apply faithful_marking_injective E A (j ≫ f)
  apply Over.OverMorphism.ext
  change ((k.left ≫ f.left) ≫ (faithfulInclusion E A).left) ≫ (value E A a).left =
    ((k.left ≫ f.left) ≫ (faithfulInclusion E A).left) ≫ (value E A b).left
  have he := congrArg (fun s ↦ s.left ≫ pullback.fst E.hom g) hab
  simpa only [Over.comp_left, Category.assoc, faithfulSectionMarking_fst] using he

end FLT.Mazur.AuxiliaryLevel
