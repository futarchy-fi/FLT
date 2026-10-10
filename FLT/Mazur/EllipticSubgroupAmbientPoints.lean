/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSubgroupAmbientClosedImmersion
public import FLT.Mazur.EllipticSubgroupSectionGenericCompatibility
public import FLT.Mazur.WeierstrassProjectivePointComparison

/-!
# The closure's ambient morphism retains the prescribed subgroup points

The generic chart evaluations and the integral sections map to the original
projective points under the constructed closed immersion into the cubic.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.EllipticSubgroupChart

open WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point) (j : Fin 3)

/-- A generic chart evaluation followed by the quotient inclusion is its original point. -/
theorem genericChartPoint_ambient (P : Index A W H j) :
    genericChartPoint A W H j P ≫ closureAmbientChart A W H j ≫ integralCurveChart W j =
      (projectiveToIntegral W P.1.1).left := by
  rw [projectiveToIntegral_chart W P.1.1 j (coordinates A W H j P)
    (coordinates_equation A W H j P) (coordinates_self A W H j P)
    (coordinates_represents A W H j P)]
  unfold genericChartPoint closureAmbientChart WeierstrassIntegralChart.integralChartPoint
  rw [← Category.assoc, ← Spec.map_comp]
  congr 1

/-- The ambient map on the generic restriction of each actual integral section. -/
theorem integralSection_generic_toCurve (P : H) :
    Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ integralSection A W H P ≫
      closureToCurve A W H 1 2 = (projectiveToIntegral W P.1).left := by
  rcases (primitiveLift A W P.1).unit_Y_or_Z A W with hy | hz
  · let Q := integralIndex A W H 1 P hy
    have he := genericChartPoint_left_section A W H Q
    change genericChartPoint A W H 1 Q ≫ _ =
      Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ integralSection A W H P at he
    rw [← Category.assoc, ← he]
    rw [Category.assoc, closureLeft_toCurve]
    exact genericChartPoint_ambient A W H 1 Q
  · let Q := integralIndex A W H 2 P hz
    have he := genericChartPoint_right_section A W H Q
    change genericChartPoint A W H 2 Q ≫ _ =
      Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ integralSection A W H P at he
    rw [← Category.assoc, ← he]
    rw [Category.assoc, closureRight_toCurve]
    exact genericChartPoint_ambient A W H 2 Q

/-- Each prescribed subgroup point has its actual generic section in the closed closure. -/
def closureGenericPoint (P : H) : Spec (.of K) ⟶ gluedClosure A W H 1 2 :=
  Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ integralSection A W H P

/-- The generic section retains exactly the original projective point in the ambient cubic. -/
@[reassoc] theorem closureGenericPoint_toCurve (P : H) :
    closureGenericPoint A W H P ≫ closureToCurve A W H 1 2 =
      (projectiveToIntegral W P.1).left :=
  (Category.assoc _ _ _).trans (integralSection_generic_toCurve A W H P)

/-- The prescribed generic point is a morphism over the field's original coefficient map. -/
@[reassoc] theorem closureGenericPoint_toBase (P : H) :
    closureGenericPoint A W H P ≫ closureToBase A W H 1 2 =
      Spec.map (CommRingCat.ofHom (algebraMap A K)) := by
  rw [closureGenericPoint, Category.assoc, integralSection_toBase, Category.comp_id]

end FLT.Mazur.EllipticSubgroupChart
