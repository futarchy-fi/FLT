/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineChartStalkScalars
public import FLT.Mazur.PolygonNodeChartNeighborhood

/-!
# Original coefficients in the complete node neighborhoods

The actual chart stalk map preserves the original stage coefficients. Hence
the complete node neighborhood comparison retains every power-series scalar.
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

/-- The actual chart stalk quotient uses the canonical coefficient germ. -/
@[simp] theorem stageChartNodeStalkQuotient_mk (m r : ℕ) (a : ChartRing (parameter K m)) :
    stageChartNodeStalkQuotient K m r (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ (StructureSheaf.toStalk (ChartRing (parameter K m))
        (stageNodePoint K m) a) := by
  let _ : Algebra (ChartRing (parameter K m))
      ((Spec (.of (ChartRing (parameter K m)))).presheaf.stalk (stageNodePoint K m)) :=
    StructureSheaf.stalkAlgebra (ChartRing (parameter K m)) (stageNodePoint K m)
  let _ : IsLocalization.AtPrime
      ((Spec (.of (ChartRing (parameter K m)))).presheaf.stalk (stageNodePoint K m))
      (coordinateIdeal (parameter K m)) :=
    StructureSheaf.IsLocalization.to_stalk (ChartRing (parameter K m)) (stageNodePoint K m)
  exact IsLocalization.AtPrime.equivQuotMaximalIdealPow_apply_mk
    (coordinateIdeal (parameter K m))
    ((Spec (.of (ChartRing (parameter K m)))).presheaf.stalk (stageNodePoint K m)) r a

variable [NeZero n] (i : Fin n) (U : (exactVeroneseProj K n h).affineOpens)
  (hx : completeNode K n h i ∈ U.1)

/-- Original structure coefficients reach the original chart's actual stalk unchanged. -/
theorem originalNodeChartStalk_scalar (m : ℕ) (s : PowerSeries K) :
    (PolygonInfinitesimal.chart (Ring K m) (parameter K m) n h i).stalkMap
      (stageNodePoint K m) ((family K m n h).left.presheaf.germ
        (originalStageToCompatibleProj K n h m ⁻¹ᵁ U) (originalStageNode K n h m i)
        (originalStageNode_mem_preimage K n h i U hx m)
        (originalStageAffineScalars K n h m U s)) =
      StructureSheaf.toStalk (ChartRing (parameter K m)) (stageNodePoint K m)
        (algebraMap (Ring K m) (ChartRing (parameter K m)) (seriesToStage K m s)) := by
  apply AffineChartStalkScalars.chart_scalar
    (PolygonInfinitesimal.chart (Ring K m) (parameter K m) n h i)
    ((family K m n h).hom ≫ baseToSeries K m)
    (CommRingCat.ofHom ((algebraMap (Ring K m) (ChartRing (parameter K m))).comp
      (seriesToStage K m).toRingHom))
  rw [← Category.assoc]
  change PolygonInfinitesimal.chart (Ring K m) (parameter K m) n h i ≫
    PolygonInfinitesimal.toBase (Ring K m) (parameter K m) n h ≫ baseToSeries K m = _
  rw [PolygonInfinitesimal.chart_toBase_assoc]
  exact (Spec.map_comp (CommRingCat.ofHom (seriesToStage K m).toRingHom)
    (CommRingCat.ofHom (algebraMap (Ring K m) (ChartRing (parameter K m))))).symm

/-- The original affine-to-chart quotient comparison preserves every complete-base scalar. -/
theorem originalNodeAffineChartQuotient_scalar (m r : ℕ) (s : PowerSeries K) :
    originalNodeAffineChartQuotient K n h i U hx m r
      (Ideal.Quotient.mk _ (originalStageAffineScalars K n h m U s)) =
        Ideal.Quotient.mk _
          (algebraMap (Ring K m) (ChartRing (parameter K m)) (seriesToStage K m s)) := by
  apply (stageChartNodeStalkQuotient K m r).injective
  rw [originalNodeAffineChartQuotient_localize, stageChartNodeStalkQuotient_mk,
    originalNodeChartStalk_scalar K n h i U hx]
  rfl

/-- The actual complete-node chart comparison retains all original coefficients. -/
theorem completeNodeChartNeighborhood_scalar (m : ℕ) (s : PowerSeries K) :
    completeNodeChartNeighborhood K n h i U hx m
      (Ideal.Quotient.mk _ (completeAffineScalars K n h U s)) =
        Ideal.Quotient.mk _
          (algebraMap (Ring K m) (ChartRing (parameter K m)) (seriesToStage K m s)) := by
  rw [completeNodeChartNeighborhood, RingEquiv.trans_apply,
    completeNodeNeighborhood_scalar, originalNodeAffineChartQuotient_scalar]

/-- The arithmetic comparison is over the original power-series base. -/
theorem completeNodeArithmeticNeighborhood_scalar (m : ℕ) (s : PowerSeries K) :
    completeNodeArithmeticNeighborhood K n h i U hx m
      (Ideal.Quotient.mk _ (completeAffineScalars K n h U s)) =
        Ideal.Quotient.mk _ (algebraMap (PowerSeries K)
          (ChartRing (PowerSeries.X : PowerSeries K)) s) := by
  apply (arithmeticNodeNeighborhood K m).injective
  rw [completeNodeArithmeticNeighborhood_toStage, completeNodeChartNeighborhood_scalar,
    arithmeticNodeNeighborhood_scalar]

end FLT.Mazur.PolygonInfinitesimalStages
