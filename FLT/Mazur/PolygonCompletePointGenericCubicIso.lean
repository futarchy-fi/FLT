/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperCurveOpenComparison
public import FLT.Mazur.PolygonCompletePointIdentityBaseChange
public import FLT.Mazur.PolygonCompleteSmoothIrreducible
public import FLT.Mazur.PolygonCompleteCartesianPointCohomology
public import FLT.Mazur.WeierstrassGenusOneFamily

/-!
# The original relative cubic comparison on nonzero-parameter field squares

The actual base change of the complete-base map is unchanged on its original
identity open. Proper integral curve comparison and the original cohomology
computations identify the entire field square with the actual changed cubic.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : Type) [Field L] (a : PowerSeries K →+* L) (ha : a PowerSeries.X ≠ 0)
  {Y : Scheme} (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom a))) (i : Fin n)
local notation "s" => Spec.map (CommRingCat.ofHom a)
local notation "W" => completePointWeierstrassCurve K n h i
local notation "c" => pullback.snd (integralCurveStructure W)
  (s ≫ Scheme.toSpecΓ (Spec (CommRingCat.of (PowerSeries K))))
local notation "f" => completePointToCubicBaseChange K n h s p q hs i
local notation "U" => completePointIdentityBaseChangeOpen K n h s i

include ha in
/-- The original relative cubic map becomes an iso on every nonzero-parameter field square. -/
theorem completePointToCubicBaseChange_isIso_of_parameter_ne_zero : IsIso (f) := by
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ : IsProper q := MorphismProperty.of_isPullback hs inferInstance
  let _ : IsProper (f ≫ c) := by
    rw [completePointToCubicBaseChange_snd]
    infer_instance
  let _ := completeCartesianField_integral K n h L a ha p q hs
  let _ := completeCartesianField_relativeDimension K n h L a ha p q hs
  let _ : IsIntegral (completePointCubicBaseChange K n h s i) :=
    integralCurveFieldSquare_isIntegral W
      (s ≫ Scheme.toSpecΓ (Spec (CommRingCat.of (PowerSeries K))))
      (pullback.fst _ _) (pullback.snd _ _) (.of_hasPullback _ _)
  let _ := completePointIdentityBaseChangeOpen_isIso K n h s p q hs i
  apply properCurve_isIso_of_open_euler_eq f U c
    (smoothCurveDimension q inferInstance inferInstance)
  · exact ⟨completePointCubicChangedZero K n h s i default,
      completePointIdentityBaseChangeOpen_zero_range K n h s i ⟨default, rfl⟩⟩
  · rw [completePointToCubicBaseChange_snd,
      completeCartesianField_structureEuler K n h L s p q hs]
    symm
    apply curveEulerCharacteristic_structure_zero
    · exact integralCurveFieldSquareH0_finrank W
        (s ≫ Scheme.toSpecΓ (Spec (CommRingCat.of (PowerSeries K))))
        (pullback.fst _ _) (pullback.snd _ _) (.of_hasPullback _ _)
    · exact integralCurveFieldSquareH1_finrank W
        (s ≫ Scheme.toSpecΓ (Spec (CommRingCat.of (PowerSeries K))))
        (pullback.fst _ _) (pullback.snd _ _) (.of_hasPullback _ _)

/-- The field-square isomorphism retains the original complete-base coordinate morphism. -/
def completePointGenericCubicIso : Y ≅ completePointCubicBaseChange K n h s i := by
  let _ := completePointToCubicBaseChange_isIso_of_parameter_ne_zero K n h L a ha p q hs i
  exact asIso (f)

/-- Projection from the generic isomorphism is the original map on the supplied family. -/
@[reassoc] theorem completePointGenericCubicIso_fst :
    (completePointGenericCubicIso K n h L a ha p q hs i).hom ≫ pullback.fst _ _ =
      p ≫ completePointToIntegralCubic K n h i :=
  completePointToCubicBaseChange_fst K n h s p q hs i

end FLT.Mazur.PolygonInfinitesimalStages
