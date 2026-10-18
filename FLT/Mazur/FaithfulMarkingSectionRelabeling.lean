/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FaithfulMarkingPullbackSections
public import FLT.Mazur.OverPullbackSection

/-!
# Relabeling faithful parameters preserves their original pulled-back sections

The actual finite relabeling action stays over the original coefficient base.
On the pulled-back group it permutes precisely the original marking labels.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.AuxiliaryLevel
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E : Over S) [GrpObj E] [IsSeparated E.hom]
  (A : Type) [Group A] [Fintype A] {T : Scheme} (g : T ⟶ S)
  (f : Over.mk g ⟶ faithfulScheme E A) (e : MulAut A)

/-- The actual faithful parameter after relabeling, over its unchanged original base. -/
def faithfulRelabeledTest : Over.mk g ⟶ faithfulScheme E A :=
  Over.homMk (f.left ≫ (faithfulAction E A e).hom) (by
    rw [Category.assoc, faithfulAction_base, f.w])

/-- The pulled-back original sections are permuted by precisely the inverse label action. -/
theorem faithfulRelabeledTest_section (a : A) :
    faithfulSectionMarking E A g (faithfulRelabeledTest E A g f e) a =
      faithfulSectionMarking E A g f (e.symm a) := by
  apply OverPullbackSection.hom_ext
  rw [faithfulSectionMarking_fst, faithfulSectionMarking_fst]
  change (f.left ≫ (faithfulAction E A e).hom) ≫ _ ≫ _ = _
  rw [Category.assoc, faithfulAction_inclusion_assoc]
  have hv : (relabelSchemeAction E e).hom ≫ (value E A a).left =
      (value E A (e.symm a)).left :=
    congrArg Over.Hom.left (relabelAction_value E e a)
  rw [hv]

/-- The same equality holds for the entire actual group-valued marking. -/
theorem faithfulRelabeledTest_marking :
    faithfulSectionMarking E A g (faithfulRelabeledTest E A g f e) =
      (faithfulSectionMarking E A g f).comp e.symm.toMonoidHom := by
  apply MonoidHom.ext
  intro a
  exact faithfulRelabeledTest_section E A g f e a

end FLT.Mazur.AuxiliaryLevel
