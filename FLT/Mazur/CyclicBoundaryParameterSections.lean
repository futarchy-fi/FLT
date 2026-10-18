/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryParameterAction
public import FLT.Mazur.OverPullbackSectionComposition
public import FLT.Mazur.GroupSectionBaseChange

/-!
# Actual boundary sections and their common relabelings

A test of the constructed boundary parameter scheme gives sections of the
original pulled-back group. Relabeling and arbitrary parameter refinement
retain these sections by exact equations in the actual fiber products.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.CyclicBoundaryParameter
open CyclicCharacteristicAtlas (RelabelGroup)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E : Over S) [GrpObj E] (n : ℕ) [NeZero n]
  {T U : Scheme} (g : T ⟶ S) (f : Over.mk g ⟶ parameter E n)

/-- The original group section associated to any boundary label and parameter test. -/
def markedSection (j : Label n) : 𝟙_ (Over T) ⟶ (Over.pullback g).obj E :=
  OverPullbackSection.lift g E (f ≫ AuxiliaryLevel.value E (Label n) j)

/-- The section retains its actual original group-valued parameter. -/
@[reassoc] theorem section_fst (j : Label n) :
    (markedSection E n g f j).left ≫ pullback.fst E.hom g =
      f.left ≫ (AuxiliaryLevel.value E (Label n) j).left :=
  OverPullbackSection.lift_fst _ _ _

/-- The common action permutes the actual original sections, on any parameter scheme. -/
theorem section_action (e : RelabelGroup n) (j : Label n) :
    markedSection E n g (f ≫ (action E n e).hom) j =
      markedSection E n g f ((labelAction n e).symm j) := by
  unfold markedSection
  rw [Category.assoc, action_value]

/-- The cyclic generator and its labels retain the prescribed independent permutation. -/
theorem section_action_cyclic (e : RelabelGroup n) (j : Multiplicative (ZMod n)) :
    markedSection E n g (f ≫ (action E n e).hom) (1, 1, j) =
      markedSection E n g f (1, 1, e.2.2.symm j) := by
  unfold markedSection
  rw [Category.assoc, action_cyclic]

/-- An arbitrary change of parameter scheme is a test of the same actual boundary scheme. -/
def refine (k : U ⟶ T) : Over.mk (k ≫ g) ⟶ parameter E n :=
  (Over.homMk k rfl : Over.mk (k ≫ g) ⟶ Over.mk g) ≫ f

/-- Refinement preserves the full original group-valued point. -/
@[reassoc] theorem refine_value (k : U ⟶ T) (j : Label n) :
    (refine E n g f k ≫ AuxiliaryLevel.value E (Label n) j).left =
      k ≫ (f ≫ AuxiliaryLevel.value E (Label n) j).left := rfl

/-- Refinement and the finite relabeling commute on the actual parameter tests. -/
theorem refine_action (k : U ⟶ T) (e : RelabelGroup n) :
    refine E n g (f ≫ (action E n e).hom) k =
      refine E n g f k ≫ (action E n e).hom := (Category.assoc _ _ _).symm

/-- The iterated section becomes the original section of the composite parameter test. -/
theorem section_refine (k : U ⟶ T) (j : Label n) :
    GroupSectionBaseChange.pullSection k (markedSection E n g f j) ≫
      (Over.pullbackComp k g).inv.app E =
        markedSection E n (k ≫ g) (refine E n g f k) j := by
  apply OverPullbackSection.hom_ext
  rw [Over.comp_left, Category.assoc, OverPullbackSection.comp_inv_fst,
    ← Category.assoc, GroupSectionBaseChange.section_fst, Category.assoc,
    section_fst, section_fst]
  rfl

end FLT.Mazur.CyclicBoundaryParameter
