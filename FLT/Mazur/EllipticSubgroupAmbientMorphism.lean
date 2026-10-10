/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSubgroupAmbientOverlap
public import FLT.Mazur.WeierstrassIntegralCurveMorphisms

/-!
# The actual subgroup closure maps into the integral cubic

The two quotient inclusions glue along their proved ambient transition.
The resulting morphism preserves the valuation-ring structure map.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits

namespace FLT.Mazur.EllipticSubgroupChart

open WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point) (j k : Fin 3)

/-- The actual closure chart quotients agree in the ambient cubic. -/
theorem closureAmbientChart_compatibility :
    closureToLeft A W H j k ≫ closureAmbientChart A W H j ≫ integralCurveChart W j =
      closureToRight A W H j k ≫ closureAmbientChart A W H k ≫ integralCurveChart W k := by
  rw [← closureAmbientOverlap_left_assoc, ← closureAmbientOverlap_right_assoc,
    integralCurveChart_compatibility]

/-- The glued subgroup closure has its canonical morphism into the original cubic. -/
def closureToCurve : gluedClosure A W H j k ⟶ integralCurve W :=
  pushout.desc (closureAmbientChart A W H j ≫ integralCurveChart W j)
    (closureAmbientChart A W H k ≫ integralCurveChart W k)
    (closureAmbientChart_compatibility A W H j k)

/-- On the first chart the ambient map is the original kernel quotient inclusion. -/
@[reassoc (attr := simp)] theorem closureLeft_toCurve :
    closureLeft A W H j k ≫ closureToCurve A W H j k =
      closureAmbientChart A W H j ≫ integralCurveChart W j := pushout.inl_desc _ _ _

/-- On the second chart the ambient map is the original kernel quotient inclusion. -/
@[reassoc (attr := simp)] theorem closureRight_toCurve :
    closureRight A W H j k ≫ closureToCurve A W H j k =
      closureAmbientChart A W H k ≫ integralCurveChart W k := pushout.inr_desc _ _ _

/-- Each chart quotient inclusion is a morphism over the original valuation ring. -/
@[reassoc] theorem closureAmbientChart_structure :
    closureAmbientChart A W H j ≫ chartStructure W j = closureChartToBase A W H j := by
  rw [closureAmbientChart, chartStructure, closureChartToBase, ← Spec.map_comp]
  rfl

/-- The global ambient map preserves the original structural morphism. -/
@[reassoc] theorem closureToCurve_structure :
    closureToCurve A W H j k ≫ integralCurveStructure W = closureToBase A W H j k := by
  apply pushout.hom_ext
  · change closureLeft A W H j k ≫ _ = closureLeft A W H j k ≫ _
    rw [closureLeft_toCurve_assoc, integralCurveChart_structure,
      closureAmbientChart_structure, closureLeft_toBase]
  · change closureRight A W H j k ≫ _ = closureRight A W H j k ≫ _
    rw [closureRight_toCurve_assoc, integralCurveChart_structure,
      closureAmbientChart_structure, closureRight_toBase]

/-- The actual subgroup closure and its ambient map as objects over the valuation ring. -/
def closureOverToCurve : Over.mk (closureToBase A W H j k) ⟶
    Over.mk (integralCurveStructure W) :=
  Over.homMk (closureToCurve A W H j k) (closureToCurve_structure A W H j k)

end FLT.Mazur.EllipticSubgroupChart
