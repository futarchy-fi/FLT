/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothSuccessiveOriginalFunctions
public import FLT.Mazur.WeierstrassSmoothHorizontalIntegralCubicAction
public import FLT.Mazur.WeierstrassSmoothSuccessiveIntegralRegular

/-!
# The full original cubic square on the common successive refinement

Both transported chart maps preserve every original cubic function. In
particular the genuine output gives a regular original horizontal coordinate.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassIntegralChart
open WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} {k : ℕ}
  (d : WeierstrassDividedDepth.Data W π (k + 1)) (hπ : π ≠ 0)
local notation "O" => SmoothHorizontalActionRing d
local notation "L" => SmoothSuccessiveActionOpen d hπ
local notation "A" => WeierstrassSuccessiveX.Coordinate W (π ^ k) π d.b3 d.b4 d.b6
local notation "h3" => d.factor3.trans (congrArg (· * d.b3) (pow_succ π k))
local notation "h4" => d.factor4.trans (congrArg (· * d.b4) (pow_succ π k))
local notation "h6" => d.factor6.trans (congrArg (fun s => s ^ 2 * d.b6) (pow_succ π k))
local notation "b" => WeierstrassModificationX.fromOriginal W (π ^ k * π)
  d.b3 d.b4 d.b6 h3 h4 h6

/-- The original cubic map of the successive chart, retaining the entire scale. -/
def successiveIntegralCubicMap : Coordinate W 2 →ₐ[R] A :=
  (modificationMap W (π ^ k) π d.b3 d.b4 d.b6).comp b

omit [IsDomain R] in
/-- The cubic map is the original divided contraction in normalized coordinates. -/
theorem successiveIntegralCubicMap_eq :
    successiveIntegralCubicMap d = (fromDivided W (π ^ k) π d.b3 d.b4 d.b6).comp
      (WeierstrassDilatation.fromOriginal W (π ^ k) (π * d.b3) (π * d.b4) (π ^ 2 * d.b6)
        ((h3).trans (mul_assoc _ _ _)) ((h4).trans (mul_assoc _ _ _))
        ((h6).trans (by ring))) :=
  modificationMap_fromOriginal W (π ^ k) π d.b3 d.b4 d.b6 h3 h4 h6

/-- The whole original input square commutes on the integral incidence refinement. -/
theorem smoothSuccessiveIntegralInput_cubic :
    (smoothSuccessiveIntegralInput d hπ).comp (successiveIntegralCubicMap d) =
      (IsScalarTower.toAlgHom R O L).comp (smoothHorizontalIntegralCubicInput d) := by
  apply AlgHom.ext
  intro q
  change smoothSuccessiveIntegralInput d hπ
    (modificationMap W (π ^ k) π d.b3 d.b4 d.b6 (b q)) = _
  rw [smoothSuccessiveIntegralInput_original]
  change algebraMap O L (smoothHorizontalIntegralInput d
    (successiveHorizontalEquationMap d hπ (b q))) = _
  exact congrArg (fun z : HorizontalSourceRing W (π ^ (k + 1)) =>
    algebraMap O L (smoothHorizontalIntegralInput d z))
      (AlgHom.congr_fun (successiveHorizontalEquationMap_fromOriginal d hπ h3 h4 h6) q)

/-- The genuine output square commutes on precisely the same integral refinement. -/
theorem smoothSuccessiveIntegralOutput_cubic :
    (smoothSuccessiveIntegralOutput d hπ).comp (successiveIntegralCubicMap d) =
      (IsScalarTower.toAlgHom R O L).comp (smoothHorizontalIntegralCubicOutput d) := by
  apply AlgHom.ext
  intro q
  change smoothSuccessiveIntegralOutput d hπ
    (modificationMap W (π ^ k) π d.b3 d.b4 d.b6 (b q)) = _
  rw [smoothSuccessiveIntegralOutput_original]
  change algebraMap O L (smoothHorizontalIntegralOutput d
    (successiveHorizontalEquationMap d hπ (b q))) = _
  exact congrArg (fun z : HorizontalSourceRing W (π ^ (k + 1)) =>
    algebraMap O L (smoothHorizontalIntegralOutput d z))
      (AlgHom.congr_fun (successiveHorizontalEquationMap_fromOriginal d hπ h3 h4 h6) q)

/-- The original smooth parameter pulled to the common integral incidence refinement. -/
def smoothSuccessiveIntegralPoint : Spec (.of L) ⟶ (integralSmoothOpen W).toScheme :=
  Spec.map (CommRingCat.ofHom (algebraMap O L)) ≫ smoothHorizontalIntegralPoint d

/-- The retained smooth parameter has the coefficient map of the common integral source. -/
@[reassoc] theorem smoothSuccessiveIntegralPoint_structure :
    smoothSuccessiveIntegralPoint d hπ ≫ integralSmoothStructure W =
      Spec.map (CommRingCat.ofHom (algebraMap R L)) := by
  rw [smoothSuccessiveIntegralPoint, Category.assoc, smoothHorizontalIntegralPoint_structure]
  exact specAlgHom_structure (IsScalarTower.toAlgHom R O L)

/-- The transported original cubic output is the genuine integral smooth action. -/
theorem smoothSuccessiveIntegralOutput_cubic_addition :
    Spec.map (CommRingCat.ofHom
        ((smoothSuccessiveIntegralOutput d hπ).comp (successiveIntegralCubicMap d)).toRingHom) ≫
        integralCurveChart W 2 =
      leftSmoothPointAddition W (smoothSuccessiveIntegralPoint d hπ)
        (Spec.map (CommRingCat.ofHom
          ((smoothSuccessiveIntegralInput d hπ).comp (successiveIntegralCubicMap d)).toRingHom) ≫
          integralCurveChart W 2) (by
            simp only [Category.assoc, integralCurveChart_structure, chartStructure,
              specAlgHom_structure, smoothSuccessiveIntegralPoint_structure]) := by
  have h := congrArg (Spec.map (CommRingCat.ofHom (algebraMap O L)) ≫ ·)
    (smoothHorizontalIntegralCubicOutput_addition d)
  rw [← leftSmoothPointAddition_comp] at h
  simp only [smoothSuccessiveIntegralInput_cubic, smoothSuccessiveIntegralOutput_cubic,
    AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom, CommRingCat.ofHom_comp, Spec.map_comp,
    Category.assoc]
  exact h

/-- The complete output cubic map has a regular original horizontal coordinate. -/
theorem smoothSuccessiveIntegralOutput_cubic_x_regular :
    IsRegular (((smoothSuccessiveIntegralOutput d hπ).comp (successiveIntegralCubicMap d))
      (WeierstrassIntegralChart.coord W 2 0)) := by
  change IsRegular (smoothSuccessiveIntegralOutput d hπ
    (modificationMap W (π ^ k) π d.b3 d.b4 d.b6 (b (WeierstrassIntegralChart.coord W 2 0))))
  rw [WeierstrassModificationX.fromOriginal_x]
  exact smoothSuccessiveIntegralOutput_original_x_regular d hπ

end FLT.Mazur.WeierstrassIntegralChart
