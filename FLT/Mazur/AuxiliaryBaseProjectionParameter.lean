/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GroupMarkingBaseProjection
public import FLT.Mazur.AuxiliaryLevelFaithfulRepresentation

/-!
# Faithful full parameters projected to the original coefficient base

Every test over the original base mapping to the parameter is itself a test
over the extended base. Consequently the inverse adjunction preserves universal
faithfulness, and projects the entire parameter to the original marking scheme.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.AuxiliaryLevel
open GroupMarkingBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} (g : T ⟶ S) (G : Over S) [GrpObj G] [IsSeparated G.hom]
  (A : Type) [Group A] [Fintype A]

/-- Separatedness of the actual pulled-back carrier. -/
local instance : IsSeparated ((Over.pullback g).obj G).hom :=
  inferInstanceAs (IsSeparated (pullback.snd G.hom g))

/-- Project all labels of the original extended-base parameter. -/
def baseProjectionMarking {U : Over T}
    (f : U ⟶ faithfulScheme ((Over.pullback g).obj G) A) :
    A →* ((Over.map g).obj U ⟶ G) :=
  projectMarking g G U (markingOf _ A (f ≫ faithfulInclusion _ A))

/-- The projected full marking remains faithful on every original-base test. -/
theorem baseProjectionMarking_faithful {U : Over T}
    (f : U ⟶ faithfulScheme ((Over.pullback g).obj G) A) :
    UniversallyFaithful G A (liftMarking G A (baseProjectionMarking g G A f)) := by
  intro V k hV a b hab
  let V' : Over T := Over.mk (k.left ≫ U.hom)
  let k' : V' ⟶ U := Over.homMk k.left rfl
  let _ : Nonempty V'.left := hV
  apply faithful_marking_injective ((Over.pullback g).obj G) A (k' ≫ f)
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · have hh := congrArg Over.Hom.left hab
    change (k ≫ liftMarking G A _ ≫ value G A a).left =
      (k ≫ liftMarking G A _ ≫ value G A b).left at hh
    simp only [liftMarking_value, Over.comp_left] at hh
    change k.left ≫ (projectMarking g G U _ a).left =
      k.left ≫ (projectMarking g G U _ b).left at hh
    rw [projectMarking_left, projectMarking_left] at hh
    simpa only [markingOf_comp, Over.comp_left, k', Over.homMk_left, Category.assoc] using hh
  · exact (markingOf _ A ((k' ≫ f) ≫ faithfulInclusion _ A) a).w.trans
      (markingOf _ A ((k' ≫ f) ≫ faithfulInclusion _ A) b).w.symm

/-- Project the complete original parameter to the faithful scheme over the original base. -/
def baseProjectionParameter {U : Over T}
    (f : U ⟶ faithfulScheme ((Over.pullback g).obj G) A) :
    (Over.map g).obj U ⟶ faithfulScheme G A :=
  faithfulLift G A (liftMarking G A (baseProjectionMarking g G A f))
    (baseProjectionMarking_faithful g G A f)

/-- Evaluation of every projected label is its actual original pullback projection. -/
theorem baseProjectionParameter_value_left {U : Over T}
    (f : U ⟶ faithfulScheme ((Over.pullback g).obj G) A) (a : A) :
    (baseProjectionParameter g G A f ≫ faithfulInclusion G A ≫ value G A a).left =
      (f ≫ faithfulInclusion _ A ≫ value _ A a).left ≫ pullback.fst G.hom g := by
  rw [← Category.assoc, baseProjectionParameter, faithfulLift_inclusion, liftMarking_value]
  exact projectMarking_left g G U _ a

end FLT.Mazur.AuxiliaryLevel
