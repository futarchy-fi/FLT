/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GroupMarkingCartesianInverse
public import FLT.Mazur.AuxiliaryCartesianGroupParameter

/-!
# Original faithful parameters from an actual cartesian group realization

A faithful marking on the realized family gives an actual parameter for the
original family. Faithfulness is checked on all original-base tests by equipping
each such test with its induced map to the extended base.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonObj
namespace FLT.Mazur.AuxiliaryLevel
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S T : Scheme} (g : T ⟶ S) (G : CommGrp (Over S)) (H : CommGrp (Over T))
  [IsSeparated G.X.hom] [IsSeparated H.X.hom]
  (e : (Over.pullback g).mapCommGrp.obj G ≅ H) (A : Type) [Group A] [Fintype A]

/-- The entire marking returned to the original family along its actual projection. -/
def originalGroupMarking {U : Over T} (f : U ⟶ faithfulScheme H.X A) :
    A →* ((Over.map g).obj U ⟶ G.X) :=
  GroupMarkingCartesianTransport.inverseMarking g G H e U
    (markingOf H.X A (f ≫ faithfulInclusion H.X A))

omit [IsSeparated G.X.hom] in
/-- Every returned original label retains the actual cartesian projection. -/
theorem originalGroupMarking_left {U : Over T} (f : U ⟶ faithfulScheme H.X A) (a : A) :
    (originalGroupMarking g G H e A f a).left =
      (f ≫ faithfulInclusion H.X A ≫ value H.X A a).left ≫
        e.inv.hom.hom.hom.left ≫ pullback.fst G.X.hom g :=
  GroupMarkingCartesianTransport.inverseMarking_left g G H e U _ a

omit [IsSeparated G.X.hom] in
/-- The returned marking is faithful on every original-base test, with no flatness hypothesis. -/
theorem originalGroupMarking_faithful {U : Over T} (f : U ⟶ faithfulScheme H.X A) :
    UniversallyFaithful G.X A (liftMarking G.X A (originalGroupMarking g G H e A f)) := by
  intro V k hV
  let _ := hV
  let V' : Over T := Over.mk (k.left ≫ U.hom)
  let k' : V' ⟶ U := Over.homMk k.left rfl
  let _ : Nonempty V'.left := hV
  have hi := faithful_marking_injective H.X A (k' ≫ f)
  intro a b hab
  apply hi
  apply GroupMarkingCartesianTransport.point_ext g G H e V'
  change (k ≫ liftMarking G.X A _) ≫ value G.X A a =
    (k ≫ liftMarking G.X A _) ≫ value G.X A b at hab
  simp only [Category.assoc, liftMarking_value] at hab
  have he := congrArg Over.Hom.left hab
  simp only [Over.comp_left, originalGroupMarking_left, Category.assoc] at he
  exact he

/-- The actual parameter of the original family retaining the complete faithful marking. -/
def originalGroupParameter {U : Over T} (f : U ⟶ faithfulScheme H.X A) :
    (Over.map g).obj U ⟶ faithfulScheme G.X A :=
  faithfulLift G.X A (liftMarking G.X A (originalGroupMarking g G H e A f))
    (originalGroupMarking_faithful g G H e A f)

/-- The parameter realizes precisely the returned original full marking. -/
@[reassoc] theorem originalGroupParameter_value {U : Over T}
    (f : U ⟶ faithfulScheme H.X A) (a : A) :
    originalGroupParameter g G H e A f ≫ faithfulInclusion G.X A ≫ value G.X A a =
      originalGroupMarking g G H e A f a := by
  rw [← Category.assoc, originalGroupParameter, faithfulLift_inclusion, liftMarking_value]

end FLT.Mazur.AuxiliaryLevel
