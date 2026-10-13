/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonParameterNormalizationLine

/-!
# Both original node branches under arbitrary parameter translations

The translated original zero and infinity incidence maps recover the same node
frame of the moved marking line, with its canonical section and all tensor powers.
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
  (c : 𝟙_ (Over T) ⟶ (Over.pullback g).obj (G K n)) (a : Kˣ) (j i : Fin n) (d : ℕ)

local notation "τ" => Over.Hom.left (Iso.hom (translationIso K n hn p q h g c))

/-- The original zero branch retains the original family node frame in every tensor degree. -/
theorem movedNormalizationLineIso_zero_node :
    LinePullbackTriangle ((Over.pullback g).map (ProjectiveLine.zeroSection K)).left
      (((Over.pullback g).map (componentι K n i ≫ p)).left ≫ τ)
      (((Over.pullback g).map (nodeι K n i ≫ q)).left ≫ τ)
      (by rw [← Category.assoc, normalizationNode_baseChange_left K n p q g i i
          (ProjectiveLine.zeroSection K) (PolygonNodeIncidence.zero_node K n hn p q h i)])
      (tensorPowerPullbackComparison _ (movedNormalizationLineIso K n hn p q h g c a j i) d)
      (tensorPowerPullbackComparison _
        (normalizationEndpointLineIso K n hn p q h g a j i i (ProjectiveLine.zeroSection K)
          (PolygonNodeIncidence.zero_node K n hn p q h i)) d)
      (tensorPowerPullbackComparison _ (movedNodeLineIso K n hn p q h g c a j i) d) :=
  (movedNormalizationLineIso_node K n hn p q h g c a j i i (ProjectiveLine.zeroSection K)
    (PolygonNodeIncidence.zero_node K n hn p q h i)).tensorPower d

/-- The adjacent infinity branch retains exactly the same original family node frame. -/
theorem movedNormalizationLineIso_infinity_node :
    LinePullbackTriangle ((Over.pullback g).map (ProjectiveLine.infinitySection K)).left
      (((Over.pullback g).map (componentι K n (next hn i) ≫ p)).left ≫ τ)
      (((Over.pullback g).map (nodeι K n i ≫ q)).left ≫ τ)
      (by rw [← Category.assoc, normalizationNode_baseChange_left K n p q g (next hn i) i
          (ProjectiveLine.infinitySection K) (PolygonNodeIncidence.infinity_node K n hn p q h i)])
      (tensorPowerPullbackComparison _
        (movedNormalizationLineIso K n hn p q h g c a j (next hn i)) d)
      (tensorPowerPullbackComparison _
        (normalizationEndpointLineIso K n hn p q h g a j (next hn i) i
          (ProjectiveLine.infinitySection K)
          (PolygonNodeIncidence.infinity_node K n hn p q h i)) d)
      (tensorPowerPullbackComparison _ (movedNodeLineIso K n hn p q h g c a j i) d) :=
  (movedNormalizationLineIso_node K n hn p q h g c a j (next hn i) i
    (ProjectiveLine.infinitySection K)
    (PolygonNodeIncidence.infinity_node K n hn p q h i)).tensorPower d

end FLT.Mazur.PolygonParameterTranslation
