/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassGlobalModificationSmoothCover
public import FLT.Mazur.WeierstrassFractionSmoothGlobalLift
public import FLT.Mazur.WeierstrassInfinitySmoothReesLift
public import FLT.Mazur.WeierstrassGlobalModificationXOpen

/-!
# Actual action lifts on the complete single-step source refinement

Every affine Z-output member lifts to the original Rees modification, for
both fraction and infinity inputs. Every Y-output member lifts directly to
the unchanged infinity chart, and X-output members use the unchanged D(x)
open. The lifts retain the exact original action on every cover member.
Overlap compatibility and global gluing are subsequent steps.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassGlobalModification

open WeierstrassIntegralChart WeierstrassModificationReesCoordinates
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6) (hs : s ≠ 0)
  (i : (smoothActionCover W s b3 b4 b6 h3 h4 h6 hs).I₀)

/-- Every affine-output member of the entire source cover has an actual Rees lift. -/
irreducible_def smoothAffineOutputToRees
    (hi : modifiedSmoothOutputIndex W (originalInputContraction W s i.1) i.2 = 2) :
    Spec ((smoothActionCover W s b3 b4 b6 h3 h4 h6 hs).X i) ⟶
      BlowupRees.proj (modificationChartCenter W s 2) := by
  rcases i with ⟨k, j⟩
  cases k with
  | none =>
    exact infinitySmoothPresentationToRees W s b3 b4 (s * b6) h3 h4
      (by simpa only [pow_two, mul_assoc] using h6) j hi
  | some k =>
    exact fractionSmoothPresentationToRees W s b3 b4 (s * b6) h3 h4
      (by simpa only [pow_two, mul_assoc] using h6)
      (centerGenerators W s k) (centerGenerators_mem W s k) j hi

/-- All affine-output Rees lifts retain the exact original output coordinates. -/
@[reassoc] theorem smoothAffineOutputToRees_contraction
    (hi : modifiedSmoothOutputIndex W (originalInputContraction W s i.1) i.2 = 2) :
    smoothAffineOutputToRees W s b3 b4 b6 h3 h4 h6 hs i hi ≫
        BlowupRees.contraction (modificationChartCenter W s 2) =
      Spec.map (CommRingCat.ofHom
        (modifiedSmoothOutputHomAt W (originalInputContraction W s i.1) i.2 2 hi)) := by
  rcases i with ⟨k, j⟩
  cases k with
  | none =>
    rw [smoothAffineOutputToRees_def, infinitySmoothPresentationToRees_contraction]
    rfl
  | some k =>
    rw [smoothAffineOutputToRees_def, fractionSmoothPresentationToRees_contraction]
    rfl

/-- The actual affine-output lift into the whole single-step projective modification. -/
irreducible_def smoothAffineOutputToGlobal
    (hi : modifiedSmoothOutputIndex W (originalInputContraction W s i.1) i.2 = 2) :
    Spec ((smoothActionCover W s b3 b4 b6 h3 h4 h6 hs).X i) ⟶
      model W s b3 b4 b6 h3 h4 h6 hs :=
  smoothAffineOutputToRees W s b3 b4 b6 h3 h4 h6 hs i hi ≫
    (modificationProjIso W s b3 b4 b6 h3 h4 h6 hs).inv ≫
      localChart W s b3 b4 b6 h3 h4 h6 hs

/-- Every affine-output lift contracts to the actual whole-source original action. -/
@[reassoc] theorem smoothAffineOutputToGlobal_action
    (hi : modifiedSmoothOutputIndex W (originalInputContraction W s i.1) i.2 = 2) :
    smoothAffineOutputToGlobal W s b3 b4 b6 h3 h4 h6 hs i hi ≫
        contraction W s b3 b4 b6 h3 h4 h6 hs =
      (smoothActionCover W s b3 b4 b6 h3 h4 h6 hs).f i ≫
        smoothActionOriginal W s b3 b4 b6 h3 h4 h6 hs := by
  rw [smoothAffineOutputToGlobal_def, Category.assoc, Category.assoc,
    localChart_contraction, modificationProjIso_inv_contraction]
  change smoothAffineOutputToRees W s b3 b4 b6 h3 h4 h6 hs i hi ≫
    BlowupRees.contraction (modificationChartCenter W s 2) ≫ integralCurveChart W 2 = _
  rw [smoothAffineOutputToRees_contraction_assoc, modifiedSmoothOutputHomAt_addition,
    smoothActionCover_original, modifiedSmoothAffineCover_addition]

/-- Every original Y-output member lifts directly to the unchanged infinity chart. -/
def smoothInfinityOutputToGlobal
    (hi : modifiedSmoothOutputIndex W (originalInputContraction W s i.1) i.2 = 1) :
    Spec ((smoothActionCover W s b3 b4 b6 h3 h4 h6 hs).X i) ⟶
      model W s b3 b4 b6 h3 h4 h6 hs :=
  Spec.map (CommRingCat.ofHom
    (modifiedSmoothOutputHomAt W (originalInputContraction W s i.1) i.2 1 hi)) ≫
      infinityChart W s b3 b4 b6 h3 h4 h6 hs

/-- Every original Y-output lift also retains the exact whole-source original action. -/
@[reassoc] theorem smoothInfinityOutputToGlobal_action
    (hi : modifiedSmoothOutputIndex W (originalInputContraction W s i.1) i.2 = 1) :
    smoothInfinityOutputToGlobal W s b3 b4 b6 h3 h4 h6 hs i hi ≫
        contraction W s b3 b4 b6 h3 h4 h6 hs =
      (smoothActionCover W s b3 b4 b6 h3 h4 h6 hs).f i ≫
        smoothActionOriginal W s b3 b4 b6 h3 h4 h6 hs := by
  rw [smoothInfinityOutputToGlobal, Category.assoc, infinityChart_contraction,
    modifiedSmoothOutputHomAt_addition, smoothActionCover_original,
    modifiedSmoothAffineCover_addition]

/-- Every original X-output member lifts through the unchanged original X-chart. -/
def smoothXOutputToGlobal
    (hi : modifiedSmoothOutputIndex W (originalInputContraction W s i.1) i.2 = 0) :
    Spec ((smoothActionCover W s b3 b4 b6 h3 h4 h6 hs).X i) ⟶
      model W s b3 b4 b6 h3 h4 h6 hs :=
  Spec.map (CommRingCat.ofHom
    (modifiedSmoothOutputHomAt W (originalInputContraction W s i.1) i.2 0 hi)) ≫
      originalXChart W s b3 b4 b6 h3 h4 h6 hs

/-- X-output lifts preserve the original action without entering an exceptional target chart. -/
@[reassoc] theorem smoothXOutputToGlobal_action
    (hi : modifiedSmoothOutputIndex W (originalInputContraction W s i.1) i.2 = 0) :
    smoothXOutputToGlobal W s b3 b4 b6 h3 h4 h6 hs i hi ≫
        contraction W s b3 b4 b6 h3 h4 h6 hs =
      (smoothActionCover W s b3 b4 b6 h3 h4 h6 hs).f i ≫
        smoothActionOriginal W s b3 b4 b6 h3 h4 h6 hs := by
  rw [smoothXOutputToGlobal, Category.assoc, originalXChart_contraction,
    modifiedSmoothOutputHomAt_addition, smoothActionCover_original,
    modifiedSmoothAffineCover_addition]

/-- An actual lifted action map on every member of the complete source cover. -/
def smoothActionLocal : Spec ((smoothActionCover W s b3 b4 b6 h3 h4 h6 hs).X i) ⟶
    model W s b3 b4 b6 h3 h4 h6 hs :=
  if h0 : modifiedSmoothOutputIndex W (originalInputContraction W s i.1) i.2 = 0 then
    smoothXOutputToGlobal W s b3 b4 b6 h3 h4 h6 hs i h0
  else if h1 : modifiedSmoothOutputIndex W (originalInputContraction W s i.1) i.2 = 1 then
    smoothInfinityOutputToGlobal W s b3 b4 b6 h3 h4 h6 hs i h1
  else smoothAffineOutputToGlobal W s b3 b4 b6 h3 h4 h6 hs i (by omega)

/-- Every local lift retains the same actual original whole-source action. -/
@[reassoc] theorem smoothActionLocal_contraction :
    smoothActionLocal W s b3 b4 b6 h3 h4 h6 hs i ≫ contraction W s b3 b4 b6 h3 h4 h6 hs =
      (smoothActionCover W s b3 b4 b6 h3 h4 h6 hs).f i ≫
        smoothActionOriginal W s b3 b4 b6 h3 h4 h6 hs := by
  unfold smoothActionLocal
  split
  · exact smoothXOutputToGlobal_action W s b3 b4 b6 h3 h4 h6 hs i _
  · split
    · exact smoothInfinityOutputToGlobal_action W s b3 b4 b6 h3 h4 h6 hs i _
    · exact smoothAffineOutputToGlobal_action W s b3 b4 b6 h3 h4 h6 hs i _

end FLT.Mazur.WeierstrassGlobalModification
