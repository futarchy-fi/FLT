/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonScalingMarkingLine
public import FLT.Mazur.PolygonRotationMarkingLine
public import FLT.Mazur.TensorPowerPullbackSquare

/-!
# Scalar and cyclic relabeling commute on the original marking line

The actual comparisons form a commuting square, retaining both pullback
compositors and the original whole-polygon equality. Every tensor degree
inherits the same square.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonMarkedSections
open PolygonPinching FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] polygonScaling polygonRotation tensorPowerPullbackComparison
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)

/-- Scaling and rotation commute on the original complete underlying scheme. -/
theorem scaling_rotation_left (c : Kˣ) (b : ZMod n) :
    (polygonScaling K hn p q h c).left ≫ (polygonRotation K hn p q h b).left =
      (polygonRotation K hn p q h b).left ≫ (polygonScaling K hn p q h c).left :=
  congrArg Over.Hom.left (polygonScaling_rotation K hn p q h c b)

/-- The two orders of scalar and cyclic relabeling give equal actual line comparisons. -/
theorem scalingLineIso_rotation (c : Kˣ) (b : ZMod n) (a : Kˣ) (i : Fin n) :
    LinePullbackSquare (polygonScaling K hn p q h c).left
      (polygonRotation K hn p q h b).left (polygonRotation K hn p q h b).left
      (polygonScaling K hn p q h c).left (scaling_rotation_left K n hn p q h c b)
      (rotationLineIso K n hn p q h b (c * a) i)
      (scalingLineIso K n hn p q h c a i)
      (scalingLineIso K n hn p q h c a (rotateIndex b i))
      (rotationLineIso K n hn p q h b a i) :=
  divisorLineSectionCompatible_square _ _ _ _ _
    (rotationLineIso_section K n hn p q h b (c * a) i)
    (scalingLineIso_section K n hn p q h c a i)
    (scalingLineIso_section K n hn p q h c a (rotateIndex b i))
    (rotationLineIso_section K n hn p q h b a i)

/-- Scalar and cyclic relabeling commute on every actual tensor power, including zero. -/
theorem scalingLineIso_rotation_power (c : Kˣ) (b : ZMod n) (a : Kˣ) (i : Fin n) (d : ℕ) :
    LinePullbackSquare (polygonScaling K hn p q h c).left
      (polygonRotation K hn p q h b).left (polygonRotation K hn p q h b).left
      (polygonScaling K hn p q h c).left (scaling_rotation_left K n hn p q h c b)
      (tensorPowerPullbackComparison _ (rotationLineIso K n hn p q h b (c * a) i) d)
      (tensorPowerPullbackComparison _ (scalingLineIso K n hn p q h c a i) d)
      (tensorPowerPullbackComparison _
        (scalingLineIso K n hn p q h c a (rotateIndex b i)) d)
      (tensorPowerPullbackComparison _ (rotationLineIso K n hn p q h b a i) d) :=
  (scalingLineIso_rotation K n hn p q h c b a i).tensorPower d

end FLT.Mazur.PolygonMarkedSections
