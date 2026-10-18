/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonActionRotations
public import FLT.Mazur.OneGonSmoothingGenusOneFamily
public import FLT.Mazur.WeierstrassSmoothWholeAction

/-!
# Geometric rotations of the actual complete one-gon action

Every singular field fiber kills the smoothing parameter. Its retained pinching
presentation and the pulled-back action laws prove the graph condition for
all points of the actual pulled-back smooth group.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.OneGonSmoothing
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] family_lfp integralCurveStructure_finitePresentation
variable (K : Type) [Field K]
local notation "W" => equation (PowerSeries.X : PowerSeries K)
local notation "C" => family (PowerSeries.X : PowerSeries K)
local notation "H" => Grp.X (CommGrp.toGrp (integralSmoothGroup (W)))

/-- The whole cubic over the complete ring is locally of finite presentation. -/
theorem completeCurveOver_lfp : LocallyOfFinitePresentation (integralCurveOver (W)).hom :=
  family_lfp (PowerSeries.X : PowerSeries K)

attribute [local instance] completeCurveOver_lfp

/-- The actual whole action is a module object over the constructed smooth group. -/
@[instance_reducible] def completeWholeModObj : ModObj (H) (C) where
  smul := integralSmoothWholeAction (W)
  one_smul := integralSmoothWholeAction_unit (W)
  mul_smul := integralSmoothWholeAction_assoc (W)

variable {L : Type} [Field L]
  (g : Spec (.of L) ⟶ Spec (.of (PowerSeries K)))

/-- A singular field fiber necessarily kills the original smoothing parameter. -/
theorem completeSingularField_parameter
    (hs : ¬ Smooth ((Over.pullback g).obj (C)).hom) :
    (Spec.preimage g).hom PowerSeries.X = 0 := by
  by_contra ha
  let a := (Spec.preimage g).hom
  have he : Spec.map (CommRingCat.ofHom a) = g := Spec.map_preimage g
  have hp : IsPullback (pullback.fst (C).hom g) (pullback.snd (C).hom g)
      (C).hom (Spec.map (CommRingCat.ofHom a)) := by
    rw [he]
    exact IsPullback.of_hasPullback _ _
  let _ := completeCartesian_relativeDimension K L a ha _ _ hp
  apply hs
  exact SmoothOfRelativeDimension.smooth 1 (pullback.snd (C).hom g)

/-- Base change retains the actual action, its identity and its associativity. -/
@[instance_reducible] def completePullbackWholeModObj :
    ModObj ((Over.pullback g).obj (H)) ((Over.pullback g).obj (C)) where
  smul := Functor.LaxMonoidal.μ (Over.pullback g) (H) (C) ≫
    (Over.pullback g).map (integralSmoothWholeAction (W))
  one_smul := MonoidalActionMap.map_unit (Over.pullback g) _
    (integralSmoothWholeAction_unit (W))
  mul_smul := MonoidalActionMap.map_assoc (Over.pullback g) _
    (integralSmoothWholeAction_assoc (W))

/-- Every singular actual field fiber has rotations of all its components and nodes. -/
theorem completeWholeAction_fiberRotations
    (hs : ¬ Smooth ((Over.pullback g).obj (C)).hom) :
    GeneralizedCurveGraph.FiberRotations (integralSmoothWholeAction (W)) g := by
  let _ := family_lfp (PowerSeries.X : PowerSeries K)
  let _ : LocallyOfFinitePresentation (pullback.snd (C).hom g) := inferInstance
  let _ := completePullbackWholeModObj K g
  let a := (Spec.preimage g).hom
  let _ := a.toAlgebra
  have he : Spec.map (CommRingCat.ofHom a) = g := Spec.map_preimage g
  have hp : IsPullback (pullback.fst (C).hom g) (pullback.snd (C).hom g)
      (C).hom (Spec.map (CommRingCat.ofHom a)) := by
    rw [he]
    exact IsPullback.of_hasPullback _ _
  have hz := zeroCartesian_isPushout L (PowerSeries.X : PowerSeries K)
    (completeSingularField_parameter K g hs) _ _ hp
  let _ : LocallyOfFinitePresentation (Over.mk (pullback.snd (C).hom g)).hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd (C).hom g))
  let _ : LocallyOfFinitePresentation ((Over.pullback g).obj (C)).hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd (C).hom g))
  change GeneralizedCurveGraph.Rotations
    (ModObj.smul (M := (Over.pullback g).obj (H)) (X := (Over.pullback g).obj (C)))
  exact GeneralizedCurveGraph.rotations_of_oneGon
    (G := (Over.pullback g).obj (H)) (X := (Over.pullback g).obj (C)) _ _ hz

/-- The constructed complete action satisfies the full geometric rotation requirement. -/
theorem completeWholeAction_geometricRotations :
    GeneralizedCurveGraph.GeometricRotations (integralSmoothWholeAction (W)) := by
  intro L _ _ g hs
  exact completeWholeAction_fiberRotations K g hs

end FLT.Mazur.OneGonSmoothing
