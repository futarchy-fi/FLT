/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCyclicBoundaryFieldNormalization
public import FLT.Mazur.PolygonCyclicBoundaryFieldNode

/-!
# Original branch incidence in intrinsic boundary field coordinates

Both original normalization branches still meet the same translated node.
The section-preserving comparisons give the exact node-frame triangle, and
that triangle persists through every tensor degree.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.PolygonCyclicBoundary
open PolygonPinching PolygonUniversalAction PolygonParameterTranslation FCurve
open PolygonMarkingBaseChange CyclicBoundaryParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] translationIso markingIdeal movedMarkingIdeal
variable (K L : Type) [Field K] [Field L] [Algebra K L]
  (m : ℕ) [NeZero m] (hm : 0 < m)
  {C : Over (Spec (.of K))} (p : components K m ⟶ C) (q : nodes K m ⟶ C)
  (h : IsPushout (toComponents K m hm) (toNodes K m) p q)
  (n : ℕ) [NeZero n]
local notation "g" => ProjectiveLineProductCharts.parameterToBase K L
local notation "F" => Over.pullback (g)
variable (f : Over.mk (ProjectiveLineProductCharts.parameterToBase K L) ⟶
  CyclicBoundaryParameter.parameter (G K m) n)
  (a : Kˣ) (i : Fin m) (j : Multiplicative (ZMod n)) (k : Fin m)
local notation "c" => markedSection (G K m) n (g) f (1, 1, j)

variable (l : Fin m) (s : point K ⟶ component K)
  (w : s ≫ (componentι K m k ≫ p) = nodeι K m l ≫ q)

include w in
/-- Original branch incidence survives the intrinsic extension-field translation. -/
theorem extendedComponent_node :
    ((F).map s).left ≫ (extendedComponent K L m hm p q h n f j k).left =
      (extendedNode K L m hm p q h n f j l).left := by
  rw [extendedComponent, extendedNode, Over.comp_left, Over.comp_left,
    ← Category.assoc, normalizationNode_baseChange_left K m p q (g) k l s w]

/-- Either original branch recovers the exact intrinsic node-frame comparison. -/
theorem extendedNormalizationLine_node :
    LinePullbackTriangle ((F).map s).left
      (extendedComponent K L m hm p q h n f j k).left
      (extendedNode K L m hm p q h n f j l).left
      (extendedComponent_node K L m hm p q h n f j k l s w)
      (extendedNormalizationLine K L m hm p q h n f a i j k)
      (normalizationEndpointLineIso K m hm p q h (g) a i k l s w)
      (extendedNodeFrame K L m hm p q h n f a i j l) :=
  divisorLineSectionCompatible_triangle _ _ _ _
    (extendedNormalizationLine_section K L m hm p q h n f a i j k)
    (normalizationEndpointLineIso_section K m hm p q h (g) a i k l s w)
    (extendedNodeFrame_section K L m hm p q h n f a i j l)

/-- The original intrinsic incidence triangle remains exact in every tensor degree. -/
theorem extendedNormalizationLine_node_power (d : ℕ) :
    LinePullbackTriangle ((F).map s).left
      (extendedComponent K L m hm p q h n f j k).left
      (extendedNode K L m hm p q h n f j l).left
      (extendedComponent_node K L m hm p q h n f j k l s w)
      (tensorPowerPullbackComparison _
        (extendedNormalizationLine K L m hm p q h n f a i j k) d)
      (tensorPowerPullbackComparison _
        (normalizationEndpointLineIso K m hm p q h (g) a i k l s w) d)
      (tensorPowerPullbackComparison _ (extendedNodeFrame K L m hm p q h n f a i j l) d) :=
  (extendedNormalizationLine_node K L m hm p q h n f a i j k l s w).tensorPower d

end FLT.Mazur.PolygonCyclicBoundary
