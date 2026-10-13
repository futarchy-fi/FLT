/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonNormalizationNodeBaseChange

/-!
# Zero and infinity branches of the original family node frame

Both incidence branches use the same actual node comparison after arbitrary
base change. The statement retains their original labels, including the one-gon,
and all tensor degrees.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonMarkingBaseChange
open PolygonPinching FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] tensorPowerPullbackComparison
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  {T : Scheme} (g : T ⟶ Spec (.of K)) (a : Kˣ) (j i : Fin n) (d : ℕ)

/-- The original zero branch retains the original family node frame in every tensor degree. -/
theorem normalizationLineIso_zero_node :
    LinePullbackTriangle ((Over.pullback g).map (ProjectiveLine.zeroSection K)).left
      ((Over.pullback g).map (componentι K n i ≫ p)).left
      ((Over.pullback g).map (nodeι K n i ≫ q)).left
      (normalizationNode_baseChange_left K n p q g i i (ProjectiveLine.zeroSection K)
        (PolygonNodeIncidence.zero_node K n hn p q h i))
      (tensorPowerPullbackComparison _ (normalizationLineIso K n hn p q h a j i g) d)
      (tensorPowerPullbackComparison _
        (normalizationEndpointLineIso K n hn p q h g a j i i (ProjectiveLine.zeroSection K)
          (PolygonNodeIncidence.zero_node K n hn p q h i)) d)
      (tensorPowerPullbackComparison _ (nodeLineIso K n hn p q h g a j i) d) :=
  normalizationLineIso_node_power K n hn p q h g a j i i (ProjectiveLine.zeroSection K)
    (PolygonNodeIncidence.zero_node K n hn p q h i) d

/-- The adjacent infinity branch retains exactly the same original family node frame. -/
theorem normalizationLineIso_infinity_node :
    LinePullbackTriangle ((Over.pullback g).map (ProjectiveLine.infinitySection K)).left
      ((Over.pullback g).map (componentι K n (next hn i) ≫ p)).left
      ((Over.pullback g).map (nodeι K n i ≫ q)).left
      (normalizationNode_baseChange_left K n p q g (next hn i) i
        (ProjectiveLine.infinitySection K) (PolygonNodeIncidence.infinity_node K n hn p q h i))
      (tensorPowerPullbackComparison _
        (normalizationLineIso K n hn p q h a j (next hn i) g) d)
      (tensorPowerPullbackComparison _
        (normalizationEndpointLineIso K n hn p q h g a j (next hn i) i
          (ProjectiveLine.infinitySection K)
          (PolygonNodeIncidence.infinity_node K n hn p q h i)) d)
      (tensorPowerPullbackComparison _ (nodeLineIso K n hn p q h g a j i) d) :=
  normalizationLineIso_node_power K n hn p q h g a j (next hn i) i
    (ProjectiveLine.infinitySection K) (PolygonNodeIncidence.infinity_node K n hn p q h i) d

end FLT.Mazur.PolygonMarkingBaseChange
