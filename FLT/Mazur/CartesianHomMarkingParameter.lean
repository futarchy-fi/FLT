/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AuxiliaryLevelHomScheme
public import FLT.Mazur.GroupMarkingBaseProjection
public import FLT.Mazur.GroupMarkingTransport

/-!
# All homomorphism parameters through a cartesian group comparison

The group comparison and pullback adjunction identify every marking, including
markings with coincident sections. No faithful open or etaleness is required.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.AuxiliaryLevel
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} (g : T ⟶ S) (G : CommGrp (Over S)) (H : CommGrp (Over T))
  (e : H ≅ (Over.pullback g).mapCommGrp.obj G) (A : Type) [Group A] [Fintype A]

/-- Project all labels through the actual group comparison and inverse adjunction. -/
def cartesianHomParameter {U : Over T} (f : U ⟶ homScheme H.X A) :
    (Over.map g).obj U ⟶ homScheme G.X A :=
  liftMarking G.X A (GroupMarkingBaseChange.projectMarking g G.X U
    (GroupMarkingTransport.transport H ((Over.pullback g).mapCommGrp.obj G) e
      (markingOf H.X A f)))

/-- Every label keeps its original scheme map after coefficient projection. -/
theorem cartesianHomParameter_value {U : Over T} (f : U ⟶ homScheme H.X A) (a : A) :
    (cartesianHomParameter g G H e A f ≫ value G.X A a).left =
      (f ≫ value H.X A a).left ≫ e.hom.hom.hom.hom.left ≫ pullback.fst G.X.hom g := by
  rw [cartesianHomParameter, liftMarking_value, GroupMarkingBaseChange.projectMarking_left]
  change ((f ≫ value H.X A a) ≫ e.hom.hom.hom.hom).left ≫ _ = _
  rw [Over.comp_left, Category.assoc]

/-- Pulling projected labels back and undoing the group comparison restores the marking. -/
def cartesianHomOriginalParameter {U : Over T}
    (f : (Over.map g).obj U ⟶ homScheme G.X A) : U ⟶ homScheme H.X A :=
  liftMarking H.X A (GroupMarkingTransport.transport
    ((Over.pullback g).mapCommGrp.obj G) H e.symm
      (GroupMarkingBaseChange.marking g G.X U (markingOf G.X A f)))

/-- The parameter correspondence is a bijection on every test, including nonreduced tests. -/
def cartesianHomParameterEquiv (U : Over T) :
    (U ⟶ homScheme H.X A) ≃ ((Over.map g).obj U ⟶ homScheme G.X A) :=
  (markingEquiv H.X A U).trans
    ((GroupMarkingTransport.markingEquiv H ((Over.pullback g).mapCommGrp.obj G) e).trans
      ((MulEquiv.monoidHomCongrRightEquiv
        (GroupMarkingBaseChange.pointsMulEquiv g G.X U).symm).trans
        (markingEquiv G.X A ((Over.map g).obj U)).symm))

/-- The forward bijection is the explicit coefficient projection. -/
theorem cartesianHomParameterEquiv_apply (U : Over T) (f : U ⟶ homScheme H.X A) :
    cartesianHomParameterEquiv g G H e A U f = cartesianHomParameter g G H e A f := rfl

/-- Coefficient projection commutes with every morphism of tests. -/
@[reassoc] theorem cartesianHomParameter_natural {U V : Over T}
    (f : U ⟶ homScheme H.X A) (k : V ⟶ U) :
    (Over.map g).map k ≫ cartesianHomParameter g G H e A f =
      cartesianHomParameter g G H e A (k ≫ f) := by
  apply homScheme_ext
  intro a
  apply Over.OverMorphism.ext
  rw [Category.assoc, Over.comp_left, cartesianHomParameter_value,
    cartesianHomParameter_value]
  simp only [Over.map_map_left, Over.comp_left, Category.assoc]

end FLT.Mazur.AuxiliaryLevel
