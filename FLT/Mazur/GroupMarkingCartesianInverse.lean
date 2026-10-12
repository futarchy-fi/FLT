/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GroupMarkingCartesianTransport
public import FLT.Mazur.GroupMarkingBaseChangeInverse

/-!
# Recovering original markings from a cartesian group realization

The inverse pullback adjunction returns the complete marking on the original
group. Each resulting scheme map is the actual cartesian projection.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.GroupMarkingCartesianTransport
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S T : Scheme} (g : T ⟶ S) (G : CommGrp (Over S)) (H : CommGrp (Over T))
  (e : (Over.pullback g).mapCommGrp.obj G ≅ H) (U : Over T)
  {A : Type*} [Monoid A]

/-- Return every marked section to the original group over its original base. -/
def inverseMarking (m : A →* (U ⟶ H.X)) : A →* ((Over.map g).obj U ⟶ G.X) :=
  (GroupMarkingBaseChange.pointsMulEquiv g G.X U).symm.toMonoidHom.comp
    (GroupMarkingTransport.transport H ((Over.pullback g).mapCommGrp.obj G) e.symm m)

/-- The recovered marking consists of the actual original projected scheme morphisms. -/
theorem inverseMarking_left (m : A →* (U ⟶ H.X)) (a : A) :
    (inverseMarking g G H e U m a).left =
      (m a).left ≫ e.inv.hom.hom.hom.left ≫ pullback.fst G.X.hom g := by
  change ((GroupMarkingBaseChange.pointsMulEquiv g G.X U).symm
    (m a ≫ e.inv.hom.hom.hom)).left = _
  rw [GroupMarkingBaseChange.pointsMulEquiv_symm_left, Over.comp_left, Category.assoc]

/-- Returning and then transporting a full marking restores every original label. -/
theorem marking_inverseMarking (m : A →* (U ⟶ H.X)) :
    marking g G H e U (inverseMarking g G H e U m) = m := by
  apply MonoidHom.ext
  intro a
  apply point_ext g G H e U
  rw [marking_projection, inverseMarking_left]

/-- Transporting and then returning a full marking also restores every label. -/
theorem inverseMarking_marking (m : A →* ((Over.map g).obj U ⟶ G.X)) :
    inverseMarking g G H e U (marking g G H e U m) = m := by
  apply MonoidHom.ext
  intro a
  apply Over.OverMorphism.ext
  rw [inverseMarking_left, marking_projection]

end FLT.Mazur.GroupMarkingCartesianTransport
