/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonPinchingCompleteClosedComparison
public import FLT.Mazur.PolygonClosedCubicContractionIso
public import FLT.Mazur.PolygonCompletePointTorusNeighborhood

import all FLT.Mazur.PolygonPinchingCompleteClosedComparison

/-!
# Original complete cubic contractions on every pinched component and node

After the full closed-fiber comparison, the original complete cubic map
is the proved one-gon contraction. This includes every exceptional component
and every singular node. Identifying it with a separate arithmetic cubic
contraction still requires comparison with that original arithmetic morphism.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonPinching PolygonOneGonContraction
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic completeClosedFiberInclusion
variable (K : Type) [Field K] (n : ℕ) (hn : 2 ≤ n) [NeZero n]
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (hp : IsPushout (toComponents K n (by omega)) (toNodes K n) p q) (i : Fin n)
local notation "e" => pinchingCompleteClosedIso K n hn p q hp
local notation "c" => completePointToIntegralCubic K n hn i
local notation "b" => completePointCubicClosedInclusion K n hn i
local notation "J" => closedPointContractionCubicIso K n hn i
local notation "a" => contraction K n (by omega) p q hp i
local notation "p₀" => PolygonCyclicAtlas.normalization K n hn
local notation "q₀" => PolygonCyclicAtlas.nodes K n hn
local notation "h₀" => PolygonCyclicPushout.isPushout K n hn (by omega)

/-- The full complete cubic contraction agrees with the specified pinching contraction. -/
@[reassoc] theorem pinchingCompleteClosedIso_cubic :
    (e).hom ≫ pullback.fst _ _ ≫ c = (a).left ≫ (J).hom ≫ b := by
  have H := completePointToCubicBaseChange_fst K n hn (completeClosedBase K)
    (completeClosedFiberInclusion K n hn) (PolygonCyclicAtlas.toBase K n hn)
    (completeClosedFiber_isPullback K n hn) i
  change closedPointToCubic K n hn i ≫ b = completeClosedFiberInclusion K n hn ≫ c at H
  apply (hp.map (Over.forget _)).hom_ext
  · change p.left ≫ _ = p.left ≫ _
    rw [pinchingCompleteClosedIso_normalization_assoc, completeClosedFiberIso_fst_assoc,
      ← H, ← closedPointContractionCubicIso_fac]
    simp only [← Category.assoc]
    have H₀ := congrArg Over.Hom.left (normalization_contraction K n (by omega) p₀ q₀ h₀ i)
    have H₁ := congrArg Over.Hom.left (normalization_contraction K n (by omega) p q hp i)
    change (p₀).left ≫ (closedPointContraction K n hn i) = _ at H₀
    change p.left ≫ (a).left = _ at H₁
    rw [H₀, H₁]
  · change q.left ≫ _ = q.left ≫ _
    rw [pinchingCompleteClosedIso_nodes_assoc, completeClosedFiberIso_fst_assoc,
      ← H, ← closedPointContractionCubicIso_fac]
    simp only [← Category.assoc]
    have H₀ := congrArg Over.Hom.left (nodes_contraction K n (by omega) p₀ q₀ h₀ i)
    have H₁ := congrArg Over.Hom.left (nodes_contraction K n (by omega) p q hp i)
    change (q₀).left ≫ (closedPointContraction K n hn i) = _ at H₀
    change q.left ≫ (a).left = _ at H₁
    rw [H₀, H₁]

/-- Every complete omitted component goes to the original closed cubic's actual node. -/
@[reassoc] theorem pinchingCompleteClosedIso_omitted_cubic {j : Fin n} (hj : j ≠ i) :
    (componentι K n j ≫ p).left ≫ (e).hom ≫ pullback.fst _ _ ≫ c =
      (componentToPoint K ≫ targetNode K).left ≫ (J).hom ≫ b := by
  rw [pinchingCompleteClosedIso_cubic K n hn p q hp i]
  have H := congrArg Over.Hom.left (omitted_contraction K n (by omega) p q hp i hj)
  simpa only [Over.comp_left, Category.assoc] using
    congrArg (fun f => f ≫ (J).hom ≫ b) H

/-- Every singular section goes to the same original closed cubic node. -/
@[reassoc] theorem pinchingCompleteClosedIso_node_cubic (j : Fin n) :
    (nodeι K n j ≫ q).left ≫ (e).hom ≫ pullback.fst _ _ ≫ c =
      (targetNode K).left ≫ (J).hom ≫ b := by
  rw [pinchingCompleteClosedIso_cubic K n hn p q hp i]
  have H := congrArg Over.Hom.left (node_contraction K n (by omega) p q hp i j)
  simpa only [Over.comp_left, Category.assoc] using
    congrArg (fun f => f ≫ (J).hom ≫ b) H

end FLT.Mazur.PolygonInfinitesimalStages
