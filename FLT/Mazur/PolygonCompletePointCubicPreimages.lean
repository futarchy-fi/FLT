/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointMarkedCoordinates
public import FLT.Mazur.PolygonCompletePointCubicFactorization

/-!
# The actual standard-chart preimages of the complete-base cubic map

The integral cubic charts pull back to the original generator opens and Cartier complement.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve FCurve.ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  divisorLineBundle ModuleSheafTensor.tensor

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "S" => Spec (CommRingCat.of (PowerSeries K))
local notation "f" => exactVeroneseProjToBase K n h
local notation "s" => completeBaseMarking K n h i
local notation "e" => completePointSectionFrame K n h i
local notation "hI" => And.left (completeBaseMarking_relativeCartier K n h i)

local notation "L" => divisorLineBundle (Scheme.Hom.ker (s)) hI
local notation "T" => completePointProjectiveSections K n h i
local notation "W" => completePointWeierstrassCurve K n h i
open WeierstrassIntegralChart

/-- Each integral chart pulls back to the actual original generator open. -/
theorem completePointToIntegralCubic_preimage_chart (j : Fin 3) :
    completePointToIntegralCubic K n h i ⁻¹ᵁ (integralCurveChart (W) j).opensRange =
      sectionGeneratorOpen (tensorPower (L) 3) (T j) := by
  rw [← integralProjectiveMap_preimage_chart, ← Scheme.Hom.comp_preimage,
    completePointToIntegralCubic_projective, completePointToProjectiveSpace,
    sectionProjectiveMorphism_preimage_chart]
  rfl

/-- The affine cubic chart has exactly the original marked-point complement as preimage. -/
theorem completePointToIntegralCubic_preimage_z :
    completePointToIntegralCubic K n h i ⁻¹ᵁ (integralCurveChart (W) 2).opensRange =
      (s).ker.support.compl := by
  rw [← integralProjectiveMap_preimage_chart, ← Scheme.Hom.comp_preimage,
    completePointToIntegralCubic_projective, completePointToProjectiveSpace_preimage_z]

/-- Along the original marking the Y generator open is the whole base. -/
theorem completePointMarking_preimage_yGenerator :
    (s) ⁻¹ᵁ sectionGeneratorOpen (tensorPower (L) 3) (T 1) = ⊤ := by
  rw [← sectionPoleCoefficient_basicOpen (s) hI e 3,
    completePointProjectiveSections_coefficient, Matrix.cons_val_one,
    Matrix.cons_val_zero, Scheme.basicOpen_one]

/-- The marking lands in the actual integral Y chart, including over nonreduced bases. -/
theorem completePointMarking_preimage_y :
    ((s) ≫ completePointToIntegralCubic K n h i) ⁻¹ᵁ
      (integralCurveChart (W) 1).opensRange = ⊤ := by
  rw [Scheme.Hom.comp_preimage, completePointToIntegralCubic_preimage_chart,
    completePointMarking_preimage_yGenerator]

end FLT.Mazur.PolygonInfinitesimalStages
