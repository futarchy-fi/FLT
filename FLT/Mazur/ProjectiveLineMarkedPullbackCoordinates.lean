/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorLinePullback
public import FLT.Mazur.PolygonDivisorPowerPullback
public import FLT.Mazur.ProjectiveLineMarkedDualCoordinates

/-!
# Positive marked divisor powers on affine charts

These comparisons identify the pullback of the actual positive line on P1
with the affine dual ideal, for every multiplicity. They yield coordinates
on arbitrary chart sections and preserve the canonical section. Compatibility
between the two charts on the Laurent overlap is a separate assertion.
-/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.ProjectiveLineMarkedPullbackCoordinates
open FCurve ProjectiveLineMarkedCharts ProjectiveLineMarkedDualCoordinates
open PolygonDivisorNormalizationPullback
variable (K : Type u) [Field K]

/-- The positive marked divisor power pulls back to the actual powered chart ideal. -/
def chartPowerIso (a : Kˣ) (j : ProjectiveLine.chart K ⟶ ProjectiveLine.scheme K)
    [IsOpenImmersion j] (b : K) (hj : (markedPoint K a).ker.comap j = (chartPoint K b).ker)
    (m : ℕ) :
    (pullback j).obj (divisorLineBundle ((markedPoint K a).ker ^ m)
      ((relativeCartier K a).1.pow m)) ≅
    divisorLineBundle ((chartPoint K b).ker ^ m) ((effectiveCartier K b).pow m) :=
  divisorLinePullbackIsoOfEq j ((relativeCartier K a).1.pow m)
    ((effectiveCartier K b).pow m) (by rw [idealSheaf_comap_pow, hj])

/-- The left-chart comparison uses the original marked coordinate. -/
def leftPowerIso (a : Kˣ) (m : ℕ) :=
  chartPowerIso K a (ProjectiveLine.left K) a (left_ideal K a) m

/-- The right-chart comparison uses the reciprocal marked coordinate. -/
def rightPowerIso (a : Kˣ) (m : ℕ) :=
  chartPowerIso K a (ProjectiveLine.right K) (a⁻¹ : Kˣ) (right_ideal K a) m

/-- Coordinates on actual sections of the pulled-back positive divisor power. -/
def chartSectionsCoordinate (a : Kˣ) (j : ProjectiveLine.chart K ⟶ ProjectiveLine.scheme K)
    [IsOpenImmersion j] (b : K) (hj : (markedPoint K a).ker.comap j = (chartPoint K b).ker)
    (m : ℕ) :
    Γ((pullback j).obj (divisorLineBundle ((markedPoint K a).ker ^ m)
      ((relativeCartier K a).1.pow m)), ⊤) ≃ₗ[Γ(ProjectiveLine.chart K, ⊤)]
      Γ(ProjectiveLine.chart K, ⊤) :=
  ModuleSheafTensor.sectionsCongr (chartPowerIso K a j b hj m) ⊤ ≪≫ₗ
    sectionsCoordinate K b m

/-- The pulled-back canonical section has the powered regular equation as coordinate. -/
lemma chartSectionsCoordinate_canonical (a : Kˣ)
    (j : ProjectiveLine.chart K ⟶ ProjectiveLine.scheme K) [IsOpenImmersion j]
    (b : K) (hj : (markedPoint K a).ker.comap j = (chartPoint K b).ker) (m : ℕ) :
    chartSectionsCoordinate K a j b hj m
      (((pullback j).map (divisorSectionMap ((relativeCartier K a).1.pow m))).app ⊤
        ((modulePullbackUnitIso j).inv.app ⊤ (1 : Γ(ProjectiveLine.chart K, ⊤)))) =
      equation K b ^ m := by
  change sectionsCoordinate K b m ((chartPowerIso K a j b hj m).hom.app ⊤ _) = _
  rw [chartPowerIso, divisorLinePullbackIsoOfEq_section_apply, canonicalSection_coordinate]
end FLT.Mazur.ProjectiveLineMarkedPullbackCoordinates
