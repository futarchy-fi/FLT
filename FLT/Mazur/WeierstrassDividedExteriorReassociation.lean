/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedExteriorStep
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Assoc

/-!
# Each repeatable exterior step is the actual local replacement

Normalize the deeper overlap and chart by the proved parameter equalities,
then apply pushout associativity. Thus enlarging the exterior first produces
the same whole as gluing the actual local modification into the old exterior.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  {k : ℕ} (hπ : π ≠ 0) {d : Data W π k} (E : Exterior d) (e : Data W π (k + 1))
open WeierstrassSuccessiveX

/-- Actual coordinates identifying the normalized deeper boundary with the x-chart overlap. -/
def nextOverlapCoordinates : boundary e ≅ Spec (.of (XOpen W (π ^ k) π e.b3 e.b4 e.b6)) :=
  nextBoundaryIso e ≪≫ (overlapIso W (π ^ k) π e.b3 e.b4 e.b6).symm

/-- The normalized divided chart is the actual divided chart used in the local gluing. -/
def nextChartCoordinates : chart e ≅
    Spec (.of (WeierstrassDilatation.Coordinate W (π ^ k * π) e.b3 e.b4 e.b6)) :=
  WeierstrassDilatation.parameterSpecIso W (π ^ k * π) (π ^ (k + 1))
    e.b3 e.b4 e.b6 e.b3 e.b4 e.b6 (pow_succ π k).symm rfl rfl rfl

/-- Normalize only the overlap and divided chart in the enlarged exterior presentation. -/
def Exterior.advanceNormalization : (E.advance hπ e).whole ≅
    pushout (xOpenInclusion W (π ^ k) π e.b3 e.b4 e.b6 ≫ E.newX hπ e)
      (overlapToDivided W (π ^ k) π e.b3 e.b4 e.b6) :=
  asIso (pushout.map _ _ _ _ (𝟙 _) (nextChartCoordinates e).hom
    (nextOverlapCoordinates e).hom
    (by simp [Exterior.advance, Exterior.newX, nextToX, nextOverlapCoordinates, Category.assoc])
    (by
      simp only [nextOverlapCoordinates, Iso.trans_hom, Iso.symm_hom,
        overlapToDivided, Category.assoc, Iso.inv_hom_id_assoc]
      exact (WeierstrassDilatation.horizontalParameterIso_inclusion W
        (π ^ k * π) (π ^ (k + 1)) e.b3 e.b4 e.b6 e.b3 e.b4 e.b6
        (pow_succ π k).symm rfl rfl rfl).symm))

/-- Glue the actual local modification to the unchanged exterior. -/
def Exterior.localReplacement : Scheme :=
  pushout E.attach (previousToX hπ d e ≫ xChart W (π ^ k) π e.b3 e.b4 e.b6)

/-- Enlarging the exterior first gives exactly the actual whole local replacement. -/
def Exterior.advanceIso : (E.advance hπ e).whole ≅ E.localReplacement hπ e :=
  E.advanceNormalization hπ e ≪≫
    pushoutAssoc E.attach (previousToX hπ d e)
      (xOpenInclusion W (π ^ k) π e.b3 e.b4 e.b6)
      (overlapToDivided W (π ^ k) π e.b3 e.b4 e.b6)

/-- This comparison retains the unchanged original exterior inclusion. -/
@[reassoc] theorem Exterior.advanceIso_retained :
    E.retained hπ e ≫ (E.advance hπ e).exteriorChart ≫ (E.advanceIso hπ e).hom =
      pushout.inl E.attach (previousToX hπ d e ≫ xChart W (π ^ k) π e.b3 e.b4 e.b6) := by
  simp [Exterior.advanceIso, Exterior.advanceNormalization, Iso.trans_hom,
    Exterior.retained, Exterior.exteriorChart, Exterior.newX, xChart]

/-- It retains the actual deeper divided chart inclusion in the local modification. -/
@[reassoc] theorem Exterior.advanceIso_divided :
    (E.advance hπ e).dividedChart ≫ (E.advanceIso hπ e).hom =
      depthDividedChart π k W e.b3 e.b4 e.b6 ≫
        pushout.inr E.attach (previousToX hπ d e ≫ xChart W (π ^ k) π e.b3 e.b4 e.b6) := by
  simp [Exterior.advanceIso, Exterior.advanceNormalization, Iso.trans_hom,
    Exterior.dividedChart, Exterior.newX, depthDividedChart, nextChartCoordinates,
    WeierstrassDilatation.parameterSpecIso, nextDepthEquiv,
    WeierstrassSuccessiveX.dividedChart, xChart]

end FLT.Mazur.WeierstrassDividedDepth
