/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveSmoothBaseChange
public import FLT.Mazur.GeneralizedCurveGraphBaseChange

/-!
# Arbitrary base change of generalized elliptic curves

The full DR object pulls back along every scheme map, with its group
identified with the actual smooth locus. Compatible maps give a functor.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace FLT.Mazur.GeneralizedEllipticCurve

variable {S T : Scheme}

/-- The full generalized elliptic curve after arbitrary scheme base change. -/
def baseChange (E : GeneralizedEllipticCurve S) (g : T ⟶ S) :
    GeneralizedEllipticCurve T where
  curve := E.pullbackCurve g
  family := E.pullback_family g
  group := E.pullbackGroup g
  smoothIso := E.smoothPullbackIso g
  act := E.pullbackAction g
  unit_act := E.pullback_unit g
  assoc_act := E.pullback_assoc g
  restriction := by
    simpa only [E.smoothPullbackIso_inclusion g] using E.pullback_restriction g
  rotations := E.pullback_rotations g

/-- The inclusion in the new DR object is the actual pullback of the original inclusion. -/
@[simp]
theorem baseChange_inclusion (E : GeneralizedEllipticCurve S) (g : T ⟶ S) :
    (E.baseChange g).inclusion = E.pullbackInclusion g :=
  E.smoothPullbackIso_inclusion g

/-- Base change preserves compatible generalized-curve morphisms. -/
def baseChangeMap (g : T ⟶ S) {E F : GeneralizedEllipticCurve S} (f : E ⟶ F) :
    E.baseChange g ⟶ F.baseChange g where
  curve := (Over.pullback g).map f.curve
  group := (Over.pullback g).map f.group
  inclusion := by simpa only [baseChange_inclusion] using E.pullback_map_inclusion g f
  action := E.pullback_map_action g f

/-- Arbitrary scheme base change is a functor on the full DR category. -/
def baseChangeFunctor (g : T ⟶ S) :
    GeneralizedEllipticCurve S ⥤ GeneralizedEllipticCurve T where
  obj E := E.baseChange g
  map f := baseChangeMap g f
  map_id E := by
    apply Hom.ext
    · exact (Over.pullback g).map_id E.curve
    · exact (Over.pullback g).map_id E.group
  map_comp f h := by
    apply Hom.ext
    · exact (Over.pullback g).map_comp f.curve h.curve
    · exact (Over.pullback g).map_comp f.group h.group

/-- Forgetting the curve commutes with the full DR pullback functor. -/
theorem baseChangeFunctor_forgetCurve (g : T ⟶ S) :
    baseChangeFunctor g ⋙ forgetCurve = forgetCurve ⋙ Over.pullback g := rfl

/-- Forgetting the group commutes with the full DR pullback functor. -/
theorem baseChangeFunctor_forgetGroup (g : T ⟶ S) :
    baseChangeFunctor g ⋙ forgetGroup = forgetGroup ⋙ Over.pullback g := rfl

end FLT.Mazur.GeneralizedEllipticCurve
