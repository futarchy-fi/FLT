/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFreePullbackFrame
public import FLT.Mazur.FreeSheafPullbackRestriction

/-!
# Finite free frames across restriction squares

Restricting a pulled finite free frame agrees with pulling its restriction
through the actual sheaf comparison of a commuting geometric square.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.FiniteFreePullbackFrame
open FCurve ModuleGlobalEvaluationPullback
variable {X Y Z W : Scheme.{u}}

/-- The actual restriction of a free frame through canonical free coordinates. -/
def restrictFrame (i : Z ⟶ X) [IsOpenImmersion i] {M : X.Modules} {ι : Type u}
    (e : M ≅ SheafOfModules.free ι) : M.restrict i ≅ SheafOfModules.free ι :=
  (restrictFunctor i).mapIso e ≪≫ freeRestrictIso i ι

/-- Pulled free frames respect arbitrary geometric restriction squares. -/
lemma frame_restriction_square (f : X ⟶ Y) (g : Z ⟶ W)
    (i : Z ⟶ X) (j : W ⟶ Y) [IsOpenImmersion i] [IsOpenImmersion j]
    (h : i ≫ f = g ≫ j) {M : Y.Modules} {ι : Type u}
    (e : M ≅ SheafOfModules.free ι) :
    modulePullbackRestrictIso f g i j h M ≪≫ frame g (restrictFrame j e) =
      restrictFrame i (frame f e) := by
  apply Iso.ext
  dsimp only [frame, restrictFrame, Iso.trans_hom, Functor.mapIso_hom]
  simp only [Functor.map_comp, Category.assoc]
  rw [← modulePullbackRestrictIso_naturality_assoc f g i j h e.hom,
    freeIso_restriction_square]

/-- Open restriction and pullback give the same frame through their canonical comparison. -/
lemma restrictFrame_eq (i : Z ⟶ X) [IsOpenImmersion i] {M : X.Modules} {ι : Type u}
    (e : M ≅ SheafOfModules.free ι) :
    restrictFrame i e = (restrictFunctorIsoPullback i).app M ≪≫ frame i e := by
  apply Iso.ext
  dsimp only [restrictFrame, freeRestrictIso, frame, Iso.trans_hom,
    Functor.mapIso_hom, Iso.app_hom]
  rw [← Category.assoc, (restrictFunctorIsoPullback i).hom.naturality, Category.assoc]

end FLT.Mazur.FiniteFreePullbackFrame
