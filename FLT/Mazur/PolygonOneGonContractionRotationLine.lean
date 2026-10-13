/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonOneGonContractionMarkingSection
public import FLT.Mazur.PolygonOneGonContractionSymmetry
public import FLT.Mazur.PolygonRotationMarkingLine
public import FLT.Mazur.DivisorLineSectionTriangle
public import FLT.Mazur.DivisorLineTensorSectionCompatibility

/-!
# Rotation coherence of contraction marking lines and their powers

The original rotation-contraction triangle commutes on the full positive
marking line and every tensor power, with the same canonical sections.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonOneGonContraction
open PolygonPinching PolygonMarkedSections FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] contraction polygonRotation tensorPowerPullbackComparison
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q) (i : Fin n)

/-- The underlying complete schemes satisfy the original rotation-contraction triangle. -/
theorem rotation_contraction_left (b : ZMod n) :
    (polygonRotation K hn p q h b).left ≫
      (contraction K n hn p q h (rotateIndex b i)).left =
        (contraction K n hn p q h i).left :=
  congrArg Over.Hom.left (rotation_contraction K n hn p q h i b)

/-- The actual canonical marking-line comparisons commute with rotation and contraction. -/
theorem markingLineIso_rotation (b : ZMod n) (a : Kˣ) :
    LinePullbackTriangle (polygonRotation K hn p q h b).left
      (contraction K n hn p q h (rotateIndex b i)).left (contraction K n hn p q h i).left
      (rotation_contraction_left K n hn p q h i b)
      (markingLineIso K n hn p q h (rotateIndex b i) a)
      (rotationLineIso K n hn p q h b a i) (markingLineIso K n hn p q h i a) :=
  divisorLineSectionCompatible_triangle _ _ _ _
    (markingLineIso_section K n hn p q h (rotateIndex b i) a)
    (rotationLineIso_section K n hn p q h b a i)
    (markingLineIso_section K n hn p q h i a)

/-- Rotation preserves every powered canonical section on the full reducible polygon. -/
theorem rotationLineIso_power_section (b : ZMod n) (a : Kˣ) (d : ℕ) :
    DivisorLinePowerSectionCompatible (polygonRotation K hn p q h b).left
      (section_cartier K n p hn q h a (rotateIndex b i)).1
      (section_cartier K n p hn q h a i).1 (rotationLineIso K n hn p q h b a i) d :=
  (rotationLineIso_section K n hn p q h b a i).tensorPower_section d

/-- The original rotation-contraction triangle commutes on every actual tensor power. -/
theorem markingLineIso_rotation_power (b : ZMod n) (a : Kˣ) (d : ℕ) :
    LinePullbackTriangle (polygonRotation K hn p q h b).left
      (contraction K n hn p q h (rotateIndex b i)).left (contraction K n hn p q h i).left
      (rotation_contraction_left K n hn p q h i b)
      (tensorPowerPullbackComparison _ (markingLineIso K n hn p q h (rotateIndex b i) a) d)
      (tensorPowerPullbackComparison _ (rotationLineIso K n hn p q h b a i) d)
      (tensorPowerPullbackComparison _ (markingLineIso K n hn p q h i a) d) :=
  (markingLineIso_rotation K n hn p q h i b a).tensorPower d

end FLT.Mazur.PolygonOneGonContraction
