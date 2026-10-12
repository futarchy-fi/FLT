/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GroupMarkingCartesianTransport
public import FLT.Mazur.AuxiliaryLevelGroupTransport

/-!
# Faithful parameters on an actual cartesian group realization

The actual group comparison transports complete faithful markings and gives
maps into the faithful marking open. The construction retains the original
parameter and every original labeled scheme map after projection.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonObj
namespace FLT.Mazur.AuxiliaryLevel
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S T : Scheme} (g : T ⟶ S) (G : CommGrp (Over S)) (H : CommGrp (Over T))
  [IsSeparated G.X.hom] [IsSeparated H.X.hom]
  (e : (Over.pullback g).mapCommGrp.obj G ≅ H) (A : Type) [Group A] [Fintype A]

/-- Transport the full original marking through the actual cartesian comparison. -/
def cartesianGroupMarking {U : Over T} (f : (Over.map g).obj U ⟶ faithfulScheme G.X A) :
    A →* (U ⟶ H.X) :=
  GroupMarkingCartesianTransport.marking g G H e U
    (markingOf G.X A (f ≫ faithfulInclusion G.X A))

omit [IsSeparated H.X.hom] in
/-- Every transported label retains its original scheme map. -/
@[reassoc] theorem cartesianGroupMarking_projection {U : Over T}
    (f : (Over.map g).obj U ⟶ faithfulScheme G.X A) (a : A) :
    (cartesianGroupMarking g G H e A f a).left ≫ e.inv.hom.hom.hom.left ≫
      pullback.fst G.X.hom g = (f ≫ faithfulInclusion G.X A ≫ value G.X A a).left :=
  GroupMarkingCartesianTransport.marking_projection g G H e U _ a

omit [IsSeparated H.X.hom] in
/-- Faithfulness on all original tests implies faithfulness on all extended-base tests. -/
theorem cartesianGroupMarking_faithful {U : Over T}
    (f : (Over.map g).obj U ⟶ faithfulScheme G.X A) :
    UniversallyFaithful H.X A (liftMarking H.X A (cartesianGroupMarking g G H e A f)) := by
  intro V k hV
  let _ : Nonempty ((Over.map g).obj V).left := hV
  intro a b hab
  have hi := faithful_marking_injective G.X A ((Over.map g).map k ≫ f)
  apply hi
  apply Over.OverMorphism.ext
  change (k ≫ liftMarking H.X A _) ≫ value H.X A a =
    (k ≫ liftMarking H.X A _) ≫ value H.X A b at hab
  simp only [Category.assoc, liftMarking_value] at hab
  have he := congrArg (fun z ↦ z.left ≫ e.inv.hom.hom.hom.left ≫
    pullback.fst G.X.hom g) hab
  simp only [Over.comp_left, Category.assoc, cartesianGroupMarking_projection] at he
  exact he

/-- The transported full marking determines an actual map to the faithful marking scheme. -/
def cartesianGroupParameter {U : Over T}
    (f : (Over.map g).obj U ⟶ faithfulScheme G.X A) : U ⟶ faithfulScheme H.X A :=
  faithfulLift H.X A (liftMarking H.X A (cartesianGroupMarking g G H e A f))
    (cartesianGroupMarking_faithful g G H e A f)

/-- The parameter realizes exactly the transported original marking. -/
@[reassoc] theorem cartesianGroupParameter_value {U : Over T}
    (f : (Over.map g).obj U ⟶ faithfulScheme G.X A) (a : A) :
    cartesianGroupParameter g G H e A f ≫ faithfulInclusion H.X A ≫ value H.X A a =
      cartesianGroupMarking g G H e A f a := by
  rw [← Category.assoc, cartesianGroupParameter, faithfulLift_inclusion, liftMarking_value]

/-- The full transported parameter is natural in every original test-scheme map. -/
@[reassoc] theorem cartesianGroupParameter_natural {U V : Over T}
    (f : (Over.map g).obj U ⟶ faithfulScheme G.X A) (k : V ⟶ U) :
    k ≫ cartesianGroupParameter g G H e A f =
      cartesianGroupParameter g G H e A ((Over.map g).map k ≫ f) := by
  apply faithfulParameter_ext H A
  intro a
  rw [Category.assoc, cartesianGroupParameter_value, cartesianGroupParameter_value]
  symm
  exact GroupMarkingCartesianTransport.marking_natural g G H e U
    (markingOf G.X A (f ≫ faithfulInclusion G.X A)) k a

end FLT.Mazur.AuxiliaryLevel
