/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassGlobalModificationOriginalOpen
public import FLT.Mazur.WeierstrassIntegralCurveTwoChartCover

/-!
# The entire original X-chart is unchanged in the modification

On the X-chart the original Z coordinate is a unit. Its transition therefore
identifies the whole X-chart with the unchanged D(x) open in the original
affine chart. Embed this actual original open into the whole modification;
no singular-origin lift is used for X-output domains.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassGlobalModification

open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6) (hs : s ≠ 0)

/-- The entire original X-chart embeds through its unchanged original D(x) open. -/
def originalXChart : chartScheme W 0 ⟶ model W s b3 b4 b6 h3 h4 h6 hs :=
  inv (overlapInclusion W 0 2) ≫ chartTransition W 0 2 ≫
    originalOpen W s b3 b4 b6 h3 h4 h6 hs (coord W 2 0)
      (Ideal.subset_span (by simp))

instance originalXChart_isOpenImmersion :
    IsOpenImmersion (originalXChart W s b3 b4 b6 h3 h4 h6 hs) := by
  unfold originalXChart
  let _ : IsIso (chartTransition W 0 2) :=
    inferInstanceAs (IsIso ((integralCurveGlueData W).t ⟨0⟩ ⟨2⟩))
  infer_instance

/-- This unchanged open contracts to precisely the original X-chart. -/
@[reassoc] theorem originalXChart_contraction :
    originalXChart W s b3 b4 b6 h3 h4 h6 hs ≫
        contraction W s b3 b4 b6 h3 h4 h6 hs = integralCurveChart W 0 := by
  rw [originalXChart, Category.assoc, Category.assoc, originalOpen_contraction]
  change inv (overlapInclusion W 0 2) ≫ chartTransition W 0 2 ≫
    overlapInclusion W 2 0 ≫ integralCurveChart W 2 = integralCurveChart W 0
  rw [integralCurveChart_compatibility, IsIso.inv_hom_id_assoc]

end FLT.Mazur.WeierstrassGlobalModification
