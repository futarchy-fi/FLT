/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryMarkingLift

/-!
# The unrestricted boundary marking equivalence

Full markings in the actual pulled-back group determine parameter tests
uniquely. The inverse therefore recovers the original test, not only its
cyclic factor, and intertwines the common finite relabeling action.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.CyclicBoundaryParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} (E : Over S) [GrpObj E] (n : ℕ) [NeZero n] (g : T ⟶ S)

/-- All actual group sections determine an unrestricted parameter test uniquely. -/
theorem boundaryGroupSectionMarking_injective :
    Function.Injective (boundaryGroupSectionMarking E n g) := by
  intro f h he
  apply AuxiliaryLevel.homScheme_ext
  intro j
  apply Over.OverMorphism.ext
  have hj := congrArg (fun m => (m j).left ≫ pullback.fst E.hom g) he
  simpa only [boundaryGroupSectionMarking_apply, section_fst, Over.comp_left] using hj

/-- Reading a test's full marking and lifting it recovers the unchanged test. -/
theorem liftBoundaryMarking_boundaryGroupSectionMarking (f : Over.mk g ⟶ parameter E n) :
    liftBoundaryMarking E n g (boundaryGroupSectionMarking E n g f) = f := by
  apply boundaryGroupSectionMarking_injective E n g
  exact boundaryGroupSectionMarking_lift E n g _

/-- Unrestricted parameters represent all full label homomorphisms on the actual pullback. -/
def boundaryMarkingEquiv : (Over.mk g ⟶ parameter E n) ≃
    (Label n →* (𝟙_ (Over T) ⟶ (Over.pullback g).obj E)) where
  toFun := boundaryGroupSectionMarking E n g
  invFun := liftBoundaryMarking E n g
  left_inv := liftBoundaryMarking_boundaryGroupSectionMarking E n g
  right_inv := boundaryGroupSectionMarking_lift E n g

/-- Lifting a relabeled marking gives the actual common action on the parameter. -/
theorem liftBoundaryMarking_action
    (m : Label n →* (𝟙_ (Over T) ⟶ (Over.pullback g).obj E))
    (e : CyclicCharacteristicAtlas.RelabelGroup n) :
    liftBoundaryMarking E n g (m.comp (labelAction n e).symm.toMonoidHom) =
      liftBoundaryMarking E n g m ≫ (action E n e).hom := by
  apply boundaryGroupSectionMarking_injective E n g
  apply MonoidHom.ext
  intro j
  rw [boundaryGroupSectionMarking_lift, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    boundaryGroupSectionMarking_apply, section_action, liftBoundaryMarking_section]

end FLT.Mazur.CyclicBoundaryParameter
