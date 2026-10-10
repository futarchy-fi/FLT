/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassVariableChangeIntegralIso
public import FLT.Mazur.WeierstrassIntegralZeroSection

/-!
# The global integral coordinate change preserves the original zero section

The homogeneous origin is scaled by a unit cube. Its actual projective
scheme point is therefore fixed, as is its lift to the original cubic.
-/

@[expose] public noncomputable section

open WeierstrassCurve AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [CommRing R]

/-- The original zero section is the actual homogeneous projective point [0:1:0]. -/
@[reassoc] theorem integralCurveZero_projectiveMap (W : WeierstrassCurve R) :
    integralCurveZero W ≫ integralProjectiveMap W =
      ProjectiveSpace.unitChartPoint R (Fin 3) (RingHom.id R) ![0, 1, 0] 1 1 rfl := by
  rw [integralCurveZero, Category.assoc, integralCurveChart_projectiveMap,
    projectiveChartMap_eq_unitChartPoint, ProjectiveSpace.unitChartPoint_map]
  simp only [map_one]
  congr 1
  · exact (chartInfinityEvaluation (S := R) W).comp_algebraMap
  · funext i
    exact chartInfinityEvaluation_coord W i

/-- The ambient projective change fixes the original homogeneous zero scheme point. -/
theorem projectiveVariableChange_zero (C : VariableChange R) :
    ProjectiveSpace.unitChartPoint R (Fin 3) (RingHom.id R) ![0, 1, 0] 1 1 rfl ≫
        (WeierstrassVariableChangeLinear.projectiveIso C).hom =
      ProjectiveSpace.unitChartPoint R (Fin 3) (RingHom.id R) ![0, 1, 0] 1 1 rfl := by
  have hc : WeierstrassVariableChangeHomogeneous.coordinates C ![0, 1, 0] =
      fun i => ((C.u ^ 3 : Rˣ) : R) * (![0, 1, 0] : Fin 3 → R) i := by
    ext i
    fin_cases i <;> simp [WeierstrassVariableChangeHomogeneous.coordinates]
  have h := WeierstrassVariableChangeLinear.unitChartPoint_projectiveIso C
    (RingHom.id R) ![0, 1, 0] 1 1 1 (C.u ^ 3) rfl
    (by simp [VariableChange.map_id, WeierstrassVariableChangeHomogeneous.coordinates])
  simp only [VariableChange.map_id, hc] at h
  rw [h]
  simpa only [mul_one] using
    ProjectiveSpace.unitChartPoint_scale R (Fin 3) (RingHom.id R) ![0, 1, 0] 1 1 (C.u ^ 3) rfl

/-- The actual proper-cubic isomorphism preserves the original zero section. -/
@[reassoc] theorem integralVariableChangeIso_zero (W V : WeierstrassCurve R)
    (C : VariableChange R) (h : C • W = V) :
    integralCurveZero V ≫ (integralVariableChangeIso W V C h).hom = integralCurveZero W := by
  apply (cancel_mono (integralProjectiveMap W)).mp
  change (integralCurveZero V ≫ integralVariableChangeTo W V C h) ≫ _ = _
  rw [Category.assoc, integralVariableChangeTo_projectiveMap,
    integralCurveZero_projectiveMap_assoc, integralCurveZero_projectiveMap,
    projectiveVariableChange_zero]

end FLT.Mazur.WeierstrassIntegralChart
