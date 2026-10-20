/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonActionRotations
public import FLT.Mazur.ArithmeticOneGonFamily
public import FLT.Mazur.WeierstrassSmoothWholeAction

/-!
# Graph rotations of arithmetic one-gon degenerations

The actual smooth-by-whole action has the required geometric rotations over
arbitrary coefficient rings. Its singular field fibers have zero parameter,
so the original one-gon pushout proves the rotation condition.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.ArithmeticOneGonRotations
open OneGonSmoothing WeierstrassIntegralChart ArithmeticOneGonFieldFibers
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] family_lfp integralCurveStructure_finitePresentation
variable {R : Type} [CommRing R] (t : R)
local notation "W" => equation t
local notation "C" => family t
local notation "H" => Grp.X (CommGrp.toGrp (integralSmoothGroup (W)))

/-- The whole cubic over the coefficient ring is locally of finite presentation. -/
theorem curveOver_lfp : LocallyOfFinitePresentation (integralCurveOver (W)).hom :=
  family_lfp t

attribute [local instance] curveOver_lfp

variable {L : Type} [Field L]
  (g : Spec (.of L) ⟶ Spec (.of R))

/-- A singular field fiber necessarily kills the original smoothing parameter. -/
theorem singularField_parameter (ht : IsUnit (1 + 432 * t))
    (hs : ¬ Smooth ((Over.pullback g).obj (C)).hom) :
    (Spec.preimage g).hom t = 0 := by
  by_contra ha
  let a := (Spec.preimage g).hom
  have he : Spec.map (CommRingCat.ofHom a) = g := Spec.map_preimage g
  have hp : IsPullback (pullback.fst (C).hom g) (pullback.snd (C).hom g)
      (C).hom (Spec.map (CommRingCat.ofHom a)) := by
    rw [he]
    exact IsPullback.of_hasPullback _ _
  let _ := cartesian_relativeDimension t ht L a ha _ _ hp
  apply hs
  exact SmoothOfRelativeDimension.smooth 1 (pullback.snd (C).hom g)

/-- Base change retains the actual action, its identity and its associativity. -/
@[instance_reducible] def pullbackWholeModObj :
    ModObj ((Over.pullback g).obj (H)) ((Over.pullback g).obj (C)) where
  smul := Functor.LaxMonoidal.μ (Over.pullback g) (H) (C) ≫
    (Over.pullback g).map (integralSmoothWholeAction (W))
  one_smul := MonoidalActionMap.map_unit (Over.pullback g) _
    (integralSmoothWholeAction_unit (W))
  mul_smul := MonoidalActionMap.map_assoc (Over.pullback g) _
    (integralSmoothWholeAction_assoc (W))

/-- Every singular actual field fiber has rotations of all its components and nodes. -/
theorem wholeAction_fiberRotations (ht : IsUnit (1 + 432 * t))
    (hs : ¬ Smooth ((Over.pullback g).obj (C)).hom) :
    GeneralizedCurveGraph.FiberRotations (integralSmoothWholeAction (W)) g := by
  let _ := family_lfp t
  let _ : LocallyOfFinitePresentation (pullback.snd (C).hom g) := inferInstance
  let _ := pullbackWholeModObj t g
  let a := (Spec.preimage g).hom
  let _ := a.toAlgebra
  have he : Spec.map (CommRingCat.ofHom a) = g := Spec.map_preimage g
  have hp : IsPullback (pullback.fst (C).hom g) (pullback.snd (C).hom g)
      (C).hom (Spec.map (CommRingCat.ofHom a)) := by
    rw [he]
    exact IsPullback.of_hasPullback _ _
  have hz := zeroCartesian_isPushout L t
    (singularField_parameter t g ht hs) _ _ hp
  let _ : LocallyOfFinitePresentation (Over.mk (pullback.snd (C).hom g)).hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd (C).hom g))
  let _ : LocallyOfFinitePresentation ((Over.pullback g).obj (C)).hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd (C).hom g))
  change GeneralizedCurveGraph.Rotations
    (ModObj.smul (M := (Over.pullback g).obj (H)) (X := (Over.pullback g).obj (C)))
  exact GeneralizedCurveGraph.rotations_of_oneGon
    (G := (Over.pullback g).obj (H)) (X := (Over.pullback g).obj (C)) _ _ hz

/-- The constructed arithmetic action satisfies the full geometric rotation requirement. -/
theorem wholeAction_geometricRotations (ht : IsUnit (1 + 432 * t)) :
    GeneralizedCurveGraph.GeometricRotations (integralSmoothWholeAction (W)) := by
  intro L _ _ g hs
  exact wholeAction_fiberRotations t g ht hs

end FLT.Mazur.ArithmeticOneGonRotations
