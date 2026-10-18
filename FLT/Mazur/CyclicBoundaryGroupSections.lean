/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryParameterSections
public import FLT.Mazur.GroupMarkingBaseChange

/-!
# Boundary parameter sections as actual group homomorphisms

The pullback adjunction supplies the group law on all sections of a boundary
test. Restricting to the cyclic factor gives the actual cyclic homomorphism
in the original base-changed group, with its prescribed finite relabeling.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.CyclicBoundaryParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E : Over S) [GrpObj E] (n : ℕ) [NeZero n]
  {T : Scheme} (g : T ⟶ S) (f : Over.mk g ⟶ parameter E n)

/-- All actual label sections, with their group law from the original parameter. -/
def sectionMarking : Label n →* (𝟙_ (Over T) ⟶ (Over.pullback g).obj E) :=
  GroupMarkingBaseChange.marking g E (𝟙_ (Over T))
    (AuxiliaryLevel.markingOf E (Label n)
      ((Over.homMk (𝟙 T) (by simp) : (Over.map g).obj (𝟙_ (Over T)) ⟶ Over.mk g) ≫ f))

/-- The group-valued marking retains exactly the existing actual section of each label. -/
theorem sectionMarking_apply (j : Label n) :
    sectionMarking E n g f j = markedSection E n g f j := by
  apply OverPullbackSection.hom_ext
  rw [sectionMarking, GroupMarkingBaseChange.marking_fst, section_fst]
  change (𝟙 T ≫ f.left) ≫ (AuxiliaryLevel.value E (Label n) j).left = _
  rw [Category.id_comp]

/-- The cyclic factor is a homomorphism in the actual pulled-back smooth group. -/
def cyclicSectionMarking : Multiplicative (ZMod n) →*
    (𝟙_ (Over T) ⟶ (Over.pullback g).obj E) where
  toFun j := sectionMarking E n g f (1, 1, j)
  map_one' := (sectionMarking E n g f).map_one
  map_mul' i j := by
    simpa only [Prod.mk_mul_mk, _root_.one_mul] using
      (sectionMarking E n g f).map_mul (1, 1, i) (1, 1, j)

/-- No section is changed by bundling its original cyclic group structure. -/
theorem cyclicSectionMarking_apply (j : Multiplicative (ZMod n)) :
    cyclicSectionMarking E n g f j = markedSection E n g f (1, 1, j) :=
  sectionMarking_apply E n g f (1, 1, j)

/-- The common finite action preserves the actual cyclic homomorphism by reindexing. -/
theorem cyclicSectionMarking_action (e : CyclicCharacteristicAtlas.RelabelGroup n) :
    cyclicSectionMarking E n g (f ≫ (action E n e).hom) =
      (cyclicSectionMarking E n g f).comp e.2.2.symm.toMonoidHom := by
  apply MonoidHom.ext
  intro j
  rw [MonoidHom.comp_apply, cyclicSectionMarking_apply, cyclicSectionMarking_apply,
    section_action_cyclic, MulEquiv.coe_toMonoidHom]

end FLT.Mazur.CyclicBoundaryParameter
