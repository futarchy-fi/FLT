/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonClosedChartRotation
public import FLT.Mazur.PolygonCompleteStageRotation
public import FLT.Mazur.PolygonCompletePrincipalClosedFiber

/-!
# The complete rotation on its original closed fiber

Coefficient naturality and the original stage square identify the complete
action with the fixed-point-free action on the original closed polygon.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonInfinitesimal PolygonCyclicAtlas
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase completeRotation
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The original closed polygon rotation commutes with every stage inclusion. -/
@[reassoc] theorem closedRotation_specialFiberInclusion (m : ℕ) (a : ZMod n) :
    closedRotation K n h a ≫ specialFiberInclusion K m n h =
      specialFiberInclusion K m n h ≫ stageRotation K n h m a := by
  have he := rotation_parameterProjection (reduction K m).toRingHom
    (parameter K m) 0 (reduction_parameter K m) n h a
  change rotation K 0 n h a ≫ zeroSpecialization K m n h =
    zeroSpecialization K m n h ≫ stageRotation K n h m a at he
  rw [specialFiberInclusion, closedRotation_zeroFiberIso_assoc, he, Category.assoc]

/-- The complete rotation restricts to the original closed chart rotation. -/
@[reassoc] theorem closedRotation_completeClosedFiberInclusion (a : ZMod n) :
    closedRotation K n h a ≫ completeClosedFiberInclusion K n h =
      completeClosedFiberInclusion K n h ≫ completeRotation K n h a := by
  rw [completeClosedFiberInclusion, closedRotation_specialFiberInclusion_assoc,
    Category.assoc, originalStageToCompatibleProj_rotation]

/-- No original closed-fiber image is fixed by a nonzero complete rotation. -/
theorem completeRotation_closed_ne_self (a : ZMod n) (ha : a ≠ 0)
    (x : PolygonCyclicAtlas.scheme K n h) :
    completeRotation K n h a (completeClosedFiberInclusion K n h x) ≠
      completeClosedFiberInclusion K n h x := by
  intro he
  have hc := congrArg (fun f ↦ f x) (closedRotation_completeClosedFiberInclusion K n h a)
  exact closedRotation_ne_self K n h a ha x
    ((completeClosedFiberInclusion K n h).isClosedEmbedding.injective (hc.trans he))

end FLT.Mazur.PolygonInfinitesimalStages
