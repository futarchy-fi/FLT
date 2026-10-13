/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonOneGonContractionReflectionLine
public import FLT.Mazur.TensorPowerPullbackSquare
public import FLT.Mazur.DivisorLineTensorSectionCompatibility

/-!
# Powered marking sections and reflection of the actual contraction

Every tensor power of the original positive marking line retains its canonical
section under contraction and reflection. The actual comparisons commute with
the original reflection-contraction square in every degree.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonOneGonContraction
open PolygonPinching PolygonMarkedSections FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] contraction polygonReflection tensorPowerPullbackComparison
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q) (i : Fin n)

/-- Contraction preserves every actual tensor power of the original vanishing section. -/
theorem markingLineIso_power_section (a : Kˣ) (d : ℕ) :
    DivisorLinePowerSectionCompatible (contraction K n hn p q h i).left
      (section_cartier K 1 (PolygonAtlas.normalization K 1) (by decide)
        (PolygonAtlas.nodes K 1) (PolygonAtlas.isPushout K 1 (by decide)) a 0).1
      (section_cartier K n p hn q h a i).1 (markingLineIso K n hn p q h i a) d :=
  (markingLineIso_section K n hn p q h i a).tensorPower_section d

/-- Reflection preserves every actual tensor power of the original vanishing section. -/
theorem reflectionLineIso_power_section (a : Kˣ) (d : ℕ) :
    DivisorLinePowerSectionCompatible (polygonReflection K hn p q h).left
      (section_cartier K n p hn q h a⁻¹ (reflectIndex i)).1
      (section_cartier K n p hn q h a i).1 (reflectionLineIso K n hn p q h a i) d :=
  (reflectionLineIso_section K n hn p q h a i).tensorPower_section d

/-- The original contraction-reflection square commutes on every actual tensor power. -/
theorem markingLineIso_reflection_power (a : Kˣ) (d : ℕ) :
    LinePullbackSquare (polygonReflection K hn p q h).left
      (contraction K n hn p q h (reflectIndex i)).left
      (contraction K n hn p q h i).left (targetReflection K).left
      (reflection_contraction_left K n hn p q h i)
      (tensorPowerPullbackComparison _ (markingLineIso K n hn p q h (reflectIndex i) a⁻¹) d)
      (tensorPowerPullbackComparison _ (reflectionLineIso K n hn p q h a i) d)
      (tensorPowerPullbackComparison _ (reflectionLineIso K 1 (by decide)
        (PolygonAtlas.normalization K 1) (PolygonAtlas.nodes K 1)
        (PolygonAtlas.isPushout K 1 (by decide)) a 0) d)
      (tensorPowerPullbackComparison _ (markingLineIso K n hn p q h i a) d) :=
  (markingLineIso_reflection K n hn p q h i a).tensorPower d

end FLT.Mazur.PolygonOneGonContraction
