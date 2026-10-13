/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSinglePointLineNormalization
public import FLT.Mazur.DivisorLineTensorSectionCompatibility

/-!
# Canonical normalization sections and all their tensor powers

The actual positive single-point line on the original polygon keeps its
canonical section on its own complete normalization component in every degree.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonSinglePointLineNormalization
open PolygonPinching PolygonMarkedSections PolygonDivisorNormalizationPullback FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ownComponentIso
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)

/-- The actual normalization comparison retains the original canonical marking section. -/
theorem ownComponentIso_compatible (a : Kˣ) (i : Fin n) :
    DivisorLineSectionCompatible (componentι K n i ≫ p).left
      (section_cartier K n p hn q h a i).1
      (ProjectiveLineMarkedCharts.relativeCartier K a).1
      (ownComponentIso K n hn p q h a i) :=
  ownComponentIso_section K n hn p q h a i

/-- Every actual tensor power of the original marking section agrees on normalization. -/
theorem ownComponentIso_power_section (a : Kˣ) (i : Fin n) (d : ℕ) :
    DivisorLinePowerSectionCompatible (componentι K n i ≫ p).left
      (section_cartier K n p hn q h a i).1
      (ProjectiveLineMarkedCharts.relativeCartier K a).1
      (ownComponentIso K n hn p q h a i) d :=
  (ownComponentIso_compatible K n hn p q h a i).tensorPower_section d

end FLT.Mazur.PolygonSinglePointLineNormalization
