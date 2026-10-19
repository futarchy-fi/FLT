/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluGenericFieldChartComparison
public import FLT.FreyCurve.Serre.VeluSchemeRationalMap

/-!
# The original Vélu map on the actual scheme function fields

The proved identifications transport the original full quadratic field map to
an injection between the generic stalks of the actual source and target cubics.
The resulting spectrum map is the generic restriction of the rational map.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

variable {K : Type} [Field K] [CharZero K] [DecidableEq K]
  (E : WeierstrassCurve K) (G : AddSubgroup E.toAffine.Point) [Fintype G]
  (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q)

/-- The original Vélu formulas act on the function fields of the actual glued cubics. -/
def veluSchemeFunctionFieldHom :
    (integralCurve (curve E G)).functionField →+* (integralCurve E).functionField :=
  (sourceSchemeFunctionFieldEquiv E).toRingHom.comp
    ((veluGenericFunctionFieldHom E G hodd).toRingHom.comp
      (sourceSchemeFunctionFieldEquiv (curve E G)).symm.toRingHom)

/-- The actual function-field map is injective. -/
theorem veluSchemeFunctionFieldHom_injective :
    Function.Injective (veluSchemeFunctionFieldHom E G hodd) :=
  (veluSchemeFunctionFieldHom E G hodd).injective

/-- The actual field map retains the original full quadratic field homomorphism. -/
theorem veluSchemeFunctionFieldHom_comparison :
    (veluSchemeFunctionFieldHom E G hodd).comp
        (sourceSchemeFunctionFieldEquiv (curve E G)).toRingHom =
      (sourceSchemeFunctionFieldEquiv E).toRingHom.comp
        (veluGenericFunctionFieldHom E G hodd).toRingHom := by
  ext z
  simp [veluSchemeFunctionFieldHom]

/-- The original field map followed by the target chart is the original generic morphism. -/
@[reassoc] theorem veluGenericFunctionFieldHom_spec_chart :
    Spec.map (CommRingCat.ofHom (veluGenericFunctionFieldHom E G hodd).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (sourceGenericChart (curve E G)).toRingHom) ≫
          integralCurveChart (curve E G) 2 = veluGenericMorphism E G hodd := by
  rw [← Spec.map_comp_assoc]
  have h := congrArg AlgHom.toRingHom (veluGenericFunctionFieldHom_chart E G hodd)
  change Spec.map (CommRingCat.ofHom
    ((veluGenericFunctionFieldHom E G hodd).comp
      (sourceGenericChart (curve E G))).toRingHom) ≫ _ = _
  rw [h]
  rfl

/-- The actual scheme field injection represents the rational map at the generic point. -/
@[reassoc] theorem veluSchemeFunctionFieldHom_generic :
    Spec.map (CommRingCat.ofHom (veluSchemeFunctionFieldHom E G hodd)) ≫
        (integralCurve (curve E G)).fromSpecStalk (genericPoint (integralCurve (curve E G))) =
      veluSchemeGenericMorphism E G hodd := by
  rw [← sourceSchemeFunctionFieldEquiv_spec, ← Spec.map_comp_assoc]
  change Spec.map (CommRingCat.ofHom
    ((veluSchemeFunctionFieldHom E G hodd).comp
      (sourceSchemeFunctionFieldEquiv (curve E G)).toRingHom)) ≫ _ = _
  rw [veluSchemeFunctionFieldHom_comparison]
  change Spec.map
    (CommRingCat.ofHom (veluGenericFunctionFieldHom E G hodd).toRingHom ≫
      CommRingCat.ofHom (sourceSchemeFunctionFieldEquiv E).toRingHom) ≫ _ = _
  rw [Spec.map_comp, Category.assoc, veluGenericFunctionFieldHom_spec_chart]
  rfl

end WeierstrassCurve.Velu
