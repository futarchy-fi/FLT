/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryGroupSections

/-!
# Unrestricted boundary parameters from full group markings

Every full label homomorphism in the actual pulled-back group determines a
boundary parameter. Projection recovers all its sections, without a
faithfulness hypothesis or an etale restriction.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.CyclicBoundaryParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} (E : Over S) [GrpObj E] (n : ℕ) [NeZero n] (g : T ⟶ S)

/-- The inverse adjunction supplies the original relative marking. -/
def originalBoundaryMarking (m : Label n →* (𝟙_ (Over T) ⟶ (Over.pullback g).obj E)) :
    Label n →* ((Over.map g).obj (𝟙_ (Over T)) ⟶ E) :=
  (GroupMarkingBaseChange.pointsMulEquiv g E (𝟙_ (Over T))).symm.toMonoidHom.comp m

/-- The actual unrestricted parameter specified by every original label. -/
def liftBoundaryMarking (m : Label n →* (𝟙_ (Over T) ⟶ (Over.pullback g).obj E)) :
    Over.mk g ⟶ parameter E n :=
  (Over.homMk (𝟙 T) (by simp) : Over.mk g ⟶ (Over.map g).obj (𝟙_ (Over T))) ≫
    AuxiliaryLevel.liftMarking E (Label n) (originalBoundaryMarking E n g m)

/-- The section of every label is recovered exactly by the unrestricted parameter. -/
theorem liftBoundaryMarking_section
    (m : Label n →* (𝟙_ (Over T) ⟶ (Over.pullback g).obj E)) (j : Label n) :
    markedSection E n g (liftBoundaryMarking E n g m) j = m j := by
  apply OverPullbackSection.hom_ext
  rw [section_fst]
  have h := AuxiliaryLevel.liftMarking_value E (Label n)
    (originalBoundaryMarking E n g m) j
  have hp := GroupMarkingBaseChange.pointsMulEquiv_fst g E (𝟙_ (Over T))
    (originalBoundaryMarking E n g m j)
  have he : GroupMarkingBaseChange.pointsMulEquiv g E (𝟙_ (Over T))
      (originalBoundaryMarking E n g m j) = m j :=
    (GroupMarkingBaseChange.pointsMulEquiv g E (𝟙_ (Over T))).apply_symm_apply (m j)
  rw [he] at hp
  change (𝟙 T ≫ (AuxiliaryLevel.liftMarking E (Label n)
    (originalBoundaryMarking E n g m)).left) ≫
    (AuxiliaryLevel.value E (Label n) j).left = _
  rw [Category.id_comp]
  exact (congrArg (fun k => k.left) h).trans hp.symm

/-- Lifting and reading all group-valued labels are inverse on full markings. -/
theorem boundaryGroupSectionMarking_lift
    (m : Label n →* (𝟙_ (Over T) ⟶ (Over.pullback g).obj E)) :
    boundaryGroupSectionMarking E n g (liftBoundaryMarking E n g m) = m := by
  apply MonoidHom.ext
  intro j
  rw [boundaryGroupSectionMarking_apply, liftBoundaryMarking_section]

end FLT.Mazur.CyclicBoundaryParameter
