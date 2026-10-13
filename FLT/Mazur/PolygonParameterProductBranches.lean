/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonParameterProductNormalization
public import FLT.Mazur.PolygonParameterProductNode
public import FLT.Mazur.PolygonNormalizationNodeBaseChange

/-!
# Both original node branches of the full translated product

The translated original zero and infinity incidence maps recover the same node
frame of the full moved product line, with its canonical section and all tensor powers.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.Obj
namespace FLT.Mazur.PolygonParameterTranslation
open PolygonPinching PolygonUniversalAction PolygonMarkingBaseChange FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] tensorPowerPullbackComparison
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  {T : Scheme} (g : T ⟶ Spec (.of K))
  (c : 𝟙_ (Over T) ⟶ (Over.pullback g).obj (G K n)) (a : Fin n → Kˣ) (i : Fin n)

local notation "τ" => Over.Hom.left (Iso.hom (translationIso K n hn p q h g c))

variable (k : Fin n) (s : point K ⟶ component K)
  (w : s ≫ (componentι K n i ≫ p) = nodeι K n k ≫ q)

/-- Either original branch recovers the same canonical node frame of the whole product. -/
theorem movedProductNormalizationLineIso_node :
    LinePullbackTriangle ((Over.pullback g).map s).left
      (((Over.pullback g).map (componentι K n i ≫ p)).left ≫ τ)
      (((Over.pullback g).map (nodeι K n k ≫ q)).left ≫ τ)
      (by rw [← Category.assoc, normalizationNode_baseChange_left K n p q g i k s w])
      (movedProductNormalizationLineIso K n hn p q h g c a i)
      (normalizationEndpointLineIso K n hn p q h g (a i) i i k s w)
      (movedProductNodeLineIso K n hn p q h g c a k) :=
  divisorLineSectionCompatible_triangle _ _ _ _
    (movedProductNormalizationLineIso_section K n hn p q h g c a i)
    (normalizationEndpointLineIso_section K n hn p q h g (a i) i i k s w)
    (movedProductNodeLineIso_section K n hn p q h g c a k)

variable (d : ℕ)

/-- The original zero branch retains the original family node frame in every tensor degree. -/
theorem movedProductNormalizationLineIso_zero_node :
    LinePullbackTriangle ((Over.pullback g).map (ProjectiveLine.zeroSection K)).left
      (((Over.pullback g).map (componentι K n i ≫ p)).left ≫ τ)
      (((Over.pullback g).map (nodeι K n i ≫ q)).left ≫ τ)
      (by rw [← Category.assoc, normalizationNode_baseChange_left K n p q g i i
          (ProjectiveLine.zeroSection K) (PolygonNodeIncidence.zero_node K n hn p q h i)])
      (tensorPowerPullbackComparison _ (movedProductNormalizationLineIso K n hn p q h g c a i) d)
      (tensorPowerPullbackComparison _
        (normalizationEndpointLineIso K n hn p q h g (a i) i i i (ProjectiveLine.zeroSection K)
          (PolygonNodeIncidence.zero_node K n hn p q h i)) d)
      (tensorPowerPullbackComparison _ (movedProductNodeLineIso K n hn p q h g c a i) d) :=
  (movedProductNormalizationLineIso_node K n hn p q h g c a i i (ProjectiveLine.zeroSection K)
    (PolygonNodeIncidence.zero_node K n hn p q h i)).tensorPower d

/-- The adjacent infinity branch retains exactly the same original family node frame. -/
theorem movedProductNormalizationLineIso_infinity_node :
    LinePullbackTriangle ((Over.pullback g).map (ProjectiveLine.infinitySection K)).left
      (((Over.pullback g).map (componentι K n (next hn i) ≫ p)).left ≫ τ)
      (((Over.pullback g).map (nodeι K n i ≫ q)).left ≫ τ)
      (by rw [← Category.assoc, normalizationNode_baseChange_left K n p q g (next hn i) i
          (ProjectiveLine.infinitySection K) (PolygonNodeIncidence.infinity_node K n hn p q h i)])
      (tensorPowerPullbackComparison _
        (movedProductNormalizationLineIso K n hn p q h g c a (next hn i)) d)
      (tensorPowerPullbackComparison _
        (normalizationEndpointLineIso K n hn p q h g (a (next hn i)) (next hn i) (next hn i) i
          (ProjectiveLine.infinitySection K)
          (PolygonNodeIncidence.infinity_node K n hn p q h i)) d)
      (tensorPowerPullbackComparison _ (movedProductNodeLineIso K n hn p q h g c a i) d) :=
  (movedProductNormalizationLineIso_node K n hn p q h g c a (next hn i) i
    (ProjectiveLine.infinitySection K)
    (PolygonNodeIncidence.infinity_node K n hn p q h i)).tensorPower d

end FLT.Mazur.PolygonParameterTranslation
