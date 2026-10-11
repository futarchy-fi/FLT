/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineClosedPointQuotient
public import FLT.Mazur.PolygonCompleteNodeNeighborhood
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Actual complete node neighborhoods compared with the arithmetic chart

Localizing both affine neighborhoods at their specified closed point, and
using the original open chart stalk map, compares their ideal-power quotients.
Together with the actual stage restrictions this identifies each complete
node neighborhood with its arithmetic xy=q neighborhood. Compatibility and
complete-base scalar identities for the composite remain separate results.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

open PolygonSmoothing

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] exactVeroneseProj originalStageToCompatibleProj
attribute [local instance] originalStageToCompatibleProj_isClosedImmersion

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n)

/-- The original chart's actual stalk has the same point neighborhoods as its coordinate ring. -/
def stageChartNodeStalkQuotient (m r : ℕ) :
    (ChartRing (parameter K m) ⧸ coordinateIdeal (parameter K m) ^ r) ≃+*
      ((Spec (.of (ChartRing (parameter K m)))).presheaf.stalk (stageNodePoint K m) ⧸
        IsLocalRing.maximalIdeal
          ((Spec (.of (ChartRing (parameter K m)))).presheaf.stalk (stageNodePoint K m)) ^ r) := by
  let _ : Algebra (ChartRing (parameter K m))
      ((Spec (.of (ChartRing (parameter K m)))).presheaf.stalk (stageNodePoint K m)) :=
    StructureSheaf.stalkAlgebra (ChartRing (parameter K m)) (stageNodePoint K m)
  let _ : IsLocalization.AtPrime
      ((Spec (.of (ChartRing (parameter K m)))).presheaf.stalk (stageNodePoint K m))
      (coordinateIdeal (parameter K m)) :=
    StructureSheaf.IsLocalization.to_stalk (ChartRing (parameter K m)) (stageNodePoint K m)
  exact (IsLocalization.AtPrime.equivQuotMaximalIdealPow (coordinateIdeal (parameter K m))
    ((Spec (.of (ChartRing (parameter K m)))).presheaf.stalk (stageNodePoint K m)) r).toRingEquiv

/-- The original open chart stalk map preserves each maximal-ideal power quotient. -/
def originalStageNodeStalkQuotient (m : ℕ) (i : Fin n) (r : ℕ) :
    ((family K m n h).left.presheaf.stalk (originalStageNode K n h m i) ⧸
      IsLocalRing.maximalIdeal
        ((family K m n h).left.presheaf.stalk (originalStageNode K n h m i)) ^ r) ≃+*
      ((Spec (.of (ChartRing (parameter K m)))).presheaf.stalk (stageNodePoint K m) ⧸
        IsLocalRing.maximalIdeal
          ((Spec (.of (ChartRing (parameter K m)))).presheaf.stalk (stageNodePoint K m)) ^ r) :=
  Ideal.quotientEquiv _ _ (asIso
    ((PolygonInfinitesimal.chart (Ring K m) (parameter K m) n h i).stalkMap
      (stageNodePoint K m))).commRingCatIsoToRingEquiv (by
        rw [Ideal.map_pow]
        exact congrArg (fun J ↦ J ^ r)
          (IsLocalRing.map_maximalIdeal_of_surjective
            (asIso ((PolygonInfinitesimal.chart (Ring K m) (parameter K m) n h i).stalkMap
              (stageNodePoint K m))).commRingCatIsoToRingEquiv.toRingHom
            (asIso ((PolygonInfinitesimal.chart (Ring K m) (parameter K m) n h i).stalkMap
              (stageNodePoint K m))).commRingCatIsoToRingEquiv.surjective).symm)

/-- Stalk quotients use exactly the original chart's stalk map on representatives. -/
@[simp] theorem originalStageNodeStalkQuotient_mk (m : ℕ) (i : Fin n) (r : ℕ)
    (a : (family K m n h).left.presheaf.stalk (originalStageNode K n h m i)) :
    originalStageNodeStalkQuotient K n h m i r (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _
        ((PolygonInfinitesimal.chart (Ring K m) (parameter K m) n h i).stalkMap
          (stageNodePoint K m) a) := rfl

variable [NeZero n] (i : Fin n) (U : (exactVeroneseProj K n h).affineOpens)
  (hx : completeNode K n h i ∈ U.1)

/-- The actual affine stage node neighborhood is its original coordinate-chart neighborhood. -/
def originalNodeAffineChartQuotient (m r : ℕ) :
    (Γ((family K m n h).left, originalStageToCompatibleProj K n h m ⁻¹ᵁ U) ⧸
      originalNodeAffineIdeal K n h i U hx m ^ r) ≃+*
        (ChartRing (parameter K m) ⧸ coordinateIdeal (parameter K m) ^ r) :=
  ((AffineClosedPointQuotient.equivalence
    ⟨originalStageToCompatibleProj K n h m ⁻¹ᵁ U,
      U.2.preimage (originalStageToCompatibleProj K n h m)⟩
    ⟨originalStageNode K n h m i, originalStageNode_mem_preimage K n h i U hx m⟩
    (originalStageNode_isClosed K m n h i) r).trans
      (originalStageNodeStalkQuotient K n h m i r)).trans
        (stageChartNodeStalkQuotient K m r).symm

/-- Localizing the chart comparison recovers the actual affine germ and open-chart stalk map. -/
theorem originalNodeAffineChartQuotient_localize (m r : ℕ)
    (a : Γ((family K m n h).left, originalStageToCompatibleProj K n h m ⁻¹ᵁ U)) :
    stageChartNodeStalkQuotient K m r
        (originalNodeAffineChartQuotient K n h i U hx m r (Ideal.Quotient.mk _ a)) =
          Ideal.Quotient.mk _
            ((PolygonInfinitesimal.chart (Ring K m) (parameter K m) n h i).stalkMap
              (stageNodePoint K m) ((family K m n h).left.presheaf.germ
              (originalStageToCompatibleProj K n h m ⁻¹ᵁ U) (originalStageNode K n h m i)
              (originalStageNode_mem_preimage K n h i U hx m) a)) := by
  rw [originalNodeAffineChartQuotient, RingEquiv.trans_apply, RingEquiv.apply_symm_apply,
    RingEquiv.trans_apply]
  exact (congrArg (originalStageNodeStalkQuotient K n h m i r)
    (AffineClosedPointQuotient.equivalence_mk
      ⟨originalStageToCompatibleProj K n h m ⁻¹ᵁ U,
        U.2.preimage (originalStageToCompatibleProj K n h m)⟩
      ⟨originalStageNode K n h m i, originalStageNode_mem_preimage K n h i U hx m⟩
      (originalStageNode_isClosed K m n h i) r a)).trans
        (originalStageNodeStalkQuotient_mk K n h m i r _)

/-- The actual complete node neighborhood agrees with the original stage chart neighborhood. -/
def completeNodeChartNeighborhood (m : ℕ) :
    (Γ(exactVeroneseProj K n h, U) ⧸ completeNodeAffineIdeal K n h i U hx ^ (m + 1)) ≃+*
      (ChartRing (parameter K m) ⧸ coordinateIdeal (parameter K m) ^ (m + 1)) :=
  (completeNodeNeighborhood K n h i U hx m).trans
    (originalNodeAffineChartQuotient K n h i U hx m (m + 1))

/-- Each actual complete node neighborhood is its original arithmetic xy=q neighborhood. -/
def completeNodeArithmeticNeighborhood (m : ℕ) :
    (Γ(exactVeroneseProj K n h, U) ⧸ completeNodeAffineIdeal K n h i U hx ^ (m + 1)) ≃+*
      (ChartRing (PowerSeries.X : PowerSeries K) ⧸
        coordinateIdeal (PowerSeries.X : PowerSeries K) ^ (m + 1)) :=
  (completeNodeChartNeighborhood K n h i U hx m).trans (arithmeticNodeNeighborhood K m).symm

/-- Returning to the original stage recovers the actual chart-neighborhood comparison. -/
theorem completeNodeArithmeticNeighborhood_toStage (m : ℕ)
    (a : Γ(exactVeroneseProj K n h, U) ⧸ completeNodeAffineIdeal K n h i U hx ^ (m + 1)) :
    arithmeticNodeNeighborhood K m (completeNodeArithmeticNeighborhood K n h i U hx m a) =
      completeNodeChartNeighborhood K n h i U hx m a :=
  (arithmeticNodeNeighborhood K m).apply_symm_apply _

end FLT.Mazur.PolygonInfinitesimalStages
