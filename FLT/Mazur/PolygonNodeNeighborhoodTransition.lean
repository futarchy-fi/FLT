/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ClosedPointStalkQuotient
public import FLT.Mazur.PolygonCompleteNodeStalkMap

/-!
# Transitions of the actual complete node neighborhoods

The same complete-node arithmetic comparisons commute with adjacent ideal
powers, through the original chart restriction and actual stalk maps.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

open PolygonSmoothing ClosedPointStalkMap

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] exactVeroneseProj originalStageToCompatibleProj

variable (K : Type) [Field K]

/-- The original adjacent chart map on the specified maximal-ideal neighborhoods. -/
def stageNodeStalkTransition (m : ℕ) :
    ((Spec (.of (ChartRing (parameter K (m + 1))))).presheaf.stalk
      (stageNodePoint K (m + 1)) ⧸ IsLocalRing.maximalIdeal
        ((Spec (.of (ChartRing (parameter K (m + 1))))).presheaf.stalk
          (stageNodePoint K (m + 1))) ^ (m + 2)) →+*
      ((Spec (.of (ChartRing (parameter K m)))).presheaf.stalk (stageNodePoint K m) ⧸
        IsLocalRing.maximalIdeal
          ((Spec (.of (ChartRing (parameter K m)))).presheaf.stalk (stageNodePoint K m)) ^
            (m + 1)) :=
  quotientMap (Spec.map (CommRingCat.ofHom (stageChartRestriction K m)))
    (stageNodePoint K m) (stageNodePoint K (m + 1)) (stageChartRestriction_nodePoint m K)
    (Nat.le_succ (m + 1))

/-- The original adjacent stalk transition retains representatives exactly. -/
@[simp] theorem stageNodeStalkTransition_mk (m : ℕ)
    (a : (Spec (.of (ChartRing (parameter K (m + 1))))).presheaf.stalk
      (stageNodePoint K (m + 1))) :
    stageNodeStalkTransition K m (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ (pointMap
        (Spec.map (CommRingCat.ofHom (stageChartRestriction K m)))
        (stageNodePoint K m) (stageNodePoint K (m + 1))
        (stageChartRestriction_nodePoint m K) a) :=
  quotientMap_mk (Spec.map (CommRingCat.ofHom (stageChartRestriction K m)))
    (stageNodePoint K m) (stageNodePoint K (m + 1)) (stageChartRestriction_nodePoint m K)
    (Nat.le_succ (m + 1)) a

/-- Original chart localization commutes with the actual adjacent stalk transition. -/
theorem stageChartNodeStalkQuotient_transition (m : ℕ)
    (a : ChartRing (parameter K (m + 1)) ⧸ coordinateIdeal (parameter K (m + 1)) ^ (m + 2)) :
    stageNodeStalkTransition K m (stageChartNodeStalkQuotient K (m + 1) (m + 2) a) =
      stageChartNodeStalkQuotient K m (m + 1) (arithmeticNodeTransition K m a) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [arithmeticNodeTransition_mk]
  refine (congrArg (stageNodeStalkTransition K m)
    (stageChartNodeStalkQuotient_mk K (m + 1) (m + 2) a)).trans ?_
  refine (quotientMap_spec_mk (CommRingCat.ofHom (stageChartRestriction K m))
    (stageNodePoint K m) (stageNodePoint K (m + 1)) (stageChartRestriction_nodePoint m K)
    (Nat.le_succ (m + 1)) a).trans ?_
  exact (stageChartNodeStalkQuotient_mk K m (m + 1) (stageChartRestriction K m a)).symm

variable (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
  (U : (exactVeroneseProj K n h).affineOpens) (hx : completeNode K n h i ∈ U.1)

/-- Actual adjacent stalk maps commute on the germ of each complete affine section. -/
theorem stageNodeStalkTransition_completeGerm (m : ℕ)
    (a : Γ(exactVeroneseProj K n h, U)) :
    stageNodeStalkTransition K m (Ideal.Quotient.mk _
      (completeNodeChartStalkMap K n h i (m + 1)
        ((exactVeroneseProj K n h).presheaf.germ U (completeNode K n h i) hx a))) =
      Ideal.Quotient.mk _ (completeNodeChartStalkMap K n h i m
        ((exactVeroneseProj K n h).presheaf.germ U (completeNode K n h i) hx a)) := by
  exact quotientMap_comp_mk (Spec.map (CommRingCat.ofHom (stageChartRestriction K m)))
    (stageNodePoint K m) (stageNodePoint K (m + 1)) (stageChartRestriction_nodePoint m K)
    (Nat.le_succ (m + 1)) (completeNodeChartStalkMap K n h i (m + 1))
    (completeNodeChartStalkMap K n h i m) (completeNodeChartStalkMap_transition K n h i m)
    ((exactVeroneseProj K n h).presheaf.germ U (completeNode K n h i) hx a)

/-- The actual complete-node chart comparisons commute with the original adjacent restrictions. -/
theorem completeNodeChartNeighborhood_transition (m : ℕ)
    (a : Γ(exactVeroneseProj K n h, U) ⧸ completeNodeAffineIdeal K n h i U hx ^ (m + 2)) :
    arithmeticNodeTransition K m (completeNodeChartNeighborhood K n h i U hx (m + 1) a) =
      completeNodeChartNeighborhood K n h i U hx m
        (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (m + 1))) a) := by
  apply (stageChartNodeStalkQuotient K m (m + 1)).injective
  rw [← stageChartNodeStalkQuotient_transition]
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [Ideal.Quotient.factor_mk, completeNodeChartNeighborhood_localize,
    completeNodeChartNeighborhood_localize]
  exact stageNodeStalkTransition_completeGerm K n h i U hx m a

/-- The original arithmetic neighborhood comparisons commute at every adjacent order. -/
theorem completeNodeArithmeticNeighborhood_transition (m : ℕ)
    (a : Γ(exactVeroneseProj K n h, U) ⧸ completeNodeAffineIdeal K n h i U hx ^ (m + 2)) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (m + 1)))
      (completeNodeArithmeticNeighborhood K n h i U hx (m + 1) a) =
        completeNodeArithmeticNeighborhood K n h i U hx m
          (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (m + 1))) a) := by
  apply (arithmeticNodeNeighborhood K m).injective
  rw [← arithmeticNodeNeighborhood_transition, completeNodeArithmeticNeighborhood_toStage,
    completeNodeArithmeticNeighborhood_toStage, completeNodeChartNeighborhood_transition]

end FLT.Mazur.PolygonInfinitesimalStages
