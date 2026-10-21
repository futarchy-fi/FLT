/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AuxiliaryLevelBaseChange
public import FLT.Mazur.AuxiliaryLevelRelabeling

/-!
# Base change retains all finite label transformations

The actual equation-scheme comparison commutes with every homomorphism of
label groups, including restriction to a cyclic factor and the finite action.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.AuxiliaryLevel
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} (g : T ⟶ S) (E : Over S) [GrpObj E]
  {A B : Type} [Group A] [Fintype A] [Group B] [Fintype B]

/-- Restriction along any label homomorphism commutes with the actual base-change map. -/
@[reassoc] theorem homSchemeBaseChange_relabel (f : B →* A) :
    (homSchemeBaseChangeIso g E A).hom ≫ relabel ((Over.pullback g).obj E) f =
      (Over.pullback g).map (relabel E f) ≫ (homSchemeBaseChangeIso g E B).hom := by
  apply homScheme_ext
  intro b
  change (homSchemeBaseChangeHom g E A ≫ relabel _ f) ≫ value _ B b =
    ((Over.pullback g).map (relabel E f) ≫ homSchemeBaseChangeHom g E B) ≫ value _ B b
  rw [Category.assoc, relabel_value, homSchemeBaseChangeHom_value,
    Category.assoc, homSchemeBaseChangeHom_value, ← Functor.map_comp, relabel_value]

/-- The inverse comparison retains every original label restriction as well. -/
@[reassoc] theorem homSchemeBaseChange_inv_relabel (f : B →* A) :
    (homSchemeBaseChangeIso g E A).inv ≫ (Over.pullback g).map (relabel E f) =
      relabel ((Over.pullback g).obj E) f ≫ (homSchemeBaseChangeIso g E B).inv := by
  apply (cancel_mono (homSchemeBaseChangeIso g E B).hom).mp
  rw [Category.assoc, ← homSchemeBaseChange_relabel, Iso.inv_hom_id_assoc,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The actual finite relabeling action commutes with arbitrary change of base. -/
@[reassoc] theorem homSchemeBaseChange_action (e : MulAut A) :
    (homSchemeBaseChangeIso g E A).hom ≫
        (relabelAction ((Over.pullback g).obj E) e).hom =
      (Over.pullback g).map (relabelAction E e).hom ≫
        (homSchemeBaseChangeIso g E A).hom :=
  homSchemeBaseChange_relabel g E e.symm.toMonoidHom

end FLT.Mazur.AuxiliaryLevel
