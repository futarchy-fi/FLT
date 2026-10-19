/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluGenericChartMorphism
public import FLT.FreyCurve.Serre.VeluSourceGenericPoint
public import FLT.Mazur.WeierstrassIntegralFinitePresentation
public import Mathlib.AlgebraicGeometry.Birational.RationalMap

/-!
# The original Vélu formulas as a rational map of the actual cubics

Transport the original generic formulas through the proved source function-field
identification and spread them out. Regularity at every point and degree remain
separate tasks.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

variable {K : Type} [Field K] [CharZero K] [DecidableEq K]
  (E : WeierstrassCurve K) (G : AddSubgroup E.toAffine.Point) [Fintype G]
  (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q)

/-- The original generic formulas now have the actual source scheme function field as domain. -/
def veluSchemeGenericMorphism :
    Spec (integralCurve E).functionField ⟶ integralCurve (curve E G) :=
  Spec.map (CommRingCat.ofHom (sourceSchemeFunctionFieldEquiv E).toRingHom) ≫
    veluGenericMorphism E G hodd

/-- The transported original formulas preserve the actual source structural morphism. -/
@[reassoc] theorem veluSchemeGenericMorphism_base :
    veluSchemeGenericMorphism E G hodd ≫ integralCurveStructure (curve E G) =
      (integralCurve E).fromSpecStalk (genericPoint (integralCurve E)) ≫
        integralCurveStructure E := by
  rw [veluSchemeGenericMorphism, Category.assoc, veluGenericMorphism_base,
    ← sourceSchemeFunctionFieldEquiv_spec, Category.assoc, Category.assoc,
    integralCurveChart_structure]
  congr 1
  symm
  exact specAlgHom_structure _

/-- The original Vélu formulas spread to a rational map of the actual glued cubics. -/
def veluSchemeRationalMap : (integralCurve E).RationalMap (integralCurve (curve E G)) :=
  Scheme.RationalMap.ofFunctionField (integralCurveStructure E)
    (integralCurveStructure (curve E G)) (veluSchemeGenericMorphism E G hodd)
    (veluSchemeGenericMorphism_base E G hodd)

/-- Spreading out retains the exact original formulas on the actual generic point. -/
theorem veluSchemeRationalMap_fromFunctionField :
    (veluSchemeRationalMap E G hodd).fromFunctionField = veluSchemeGenericMorphism E G hodd :=
  Scheme.RationalMap.fromFunctionField_ofFunctionField _ _ _ _

end WeierstrassCurve.Velu
