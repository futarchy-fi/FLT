/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticFactorRatioInfinity
public import FLT.Mazur.WeierstrassChartBaseChangeSquare
public import FLT.Mazur.TensorOpenChart

/-!
# The entire original infinity tensor chart in the arithmetic polygon

The original cubic tensor equivalence transports the complete regular factor
ratio, preserving both the original integral projection and quotient scalars.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassIntegralChart WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] (π : R) (m : ℕ) (W : WeierstrassCurve R)
local notation "Q" => Quotient R π m
local notation "q" => algebraMap R Q

/-- The original arithmetic infinity tensor scheme is the full specialized cubic chart. -/
def arithmeticInfinityTensorIso : chartScheme (W.map q) 1 ≅
    Spec (.of (Q ⊗[R] WeierstrassIntegralChart.Coordinate W 1)) :=
  Scheme.Spec.mapIso (chartBaseChangeEquiv Q W 1).toRingEquiv.toCommRingCatIso.op

/-- The original infinity tensor comparison retains the actual arithmetic coefficient map. -/
@[reassoc] theorem arithmeticInfinityTensorIso_structure :
    (arithmeticInfinityTensorIso π m W).hom ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap Q (Q ⊗[R] WeierstrassIntegralChart.Coordinate W 1))) =
      chartStructure (W.map q) 1 := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext (chartBaseChangeEquiv Q W 1).commutes)

/-- The full original integral cubic coordinates survive the tensor comparison. -/
@[reassoc] theorem arithmeticInfinityTensorIso_projection :
    (arithmeticInfinityTensorIso π m W).hom ≫ TensorOpenChart.projection =
      chartCoefficientMorphism W 1 := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext fun z => one_smul Q (chartCoefficientMap (S := Q) W 1 z)

variable (s b3 b4 b6 : R) (ha : IsUnit W.a₁) (hs : π ∣ s)
  (h2 : π ∣ W.a₂) (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6)
  (h3a : π ∣ W.a₃) (h4a : π ∣ W.a₄) (h6a : π ∣ W.a₆) (k : ℕ)
local notation "τ" => arithmeticInitialMobiusSmoothing W ha s π m
local notation "hn" => Fact.mk (arithmeticInitialFactorRatioSmoothing_nilpotent W ha s π m hs)

/-- The full original infinity tensor chart maps to the polygon with its exact smoothing. -/
def arithmeticFactorRatioTensorInfinityMap :
    Spec (.of (Q ⊗[R] WeierstrassIntegralChart.Coordinate W 1)) ⟶
      arithmeticFactorRatioPolygon π m W s ha hs k :=
  (arithmeticInfinityTensorIso π m W).inv ≫
    arithmeticFactorRatioInfinityPolygonMap π m W s b3 b4 b6
      ha hs h2 h3 h4 h6 h3a h4a h6a k

/-- Transport recovers the complete original infinity factor ratio. -/
@[reassoc] theorem arithmeticFactorRatioTensorInfinityMap_transport :
    (arithmeticInfinityTensorIso π m W).hom ≫
      arithmeticFactorRatioTensorInfinityMap π m W s b3 b4 b6
        ha hs h2 h3 h4 h6 h3a h4a h6a k =
      arithmeticFactorRatioInfinityPolygonMap π m W s b3 b4 b6
        ha hs h2 h3 h4 h6 h3a h4a h6a k := by
  rw [arithmeticFactorRatioTensorInfinityMap, Iso.hom_inv_id_assoc]

/-- The full coefficient infinity comparison lies over its actual arithmetic quotient. -/
@[reassoc] theorem arithmeticFactorRatioInfinityPolygonMap_structure :
    arithmeticFactorRatioInfinityPolygonMap π m W s b3 b4 b6
      ha hs h2 h3 h4 h6 h3a h4a h6a k ≫
        @PolygonInfinitesimal.toBase Q _ τ (2 * k + 3) hn (by omega) =
      chartStructure (W.map q) 1 := by
  let _ := hn
  unfold arithmeticFactorRatioInfinityPolygonMap fullFactorRatioInfinityPolygonMap
  rw [Category.assoc, Category.assoc, PolygonInfinitesimal.chart_toBase,
    PolygonSmoothing.rightBranchOpen_base]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  exact (LaurentUnitPoints.evalUnit _).commutes z

/-- Transport preserves the full infinity tensor coefficient projection. -/
@[reassoc] theorem arithmeticFactorRatioTensorInfinityMap_structure :
    arithmeticFactorRatioTensorInfinityMap π m W s b3 b4 b6
      ha hs h2 h3 h4 h6 h3a h4a h6a k ≫
        @PolygonInfinitesimal.toBase Q _ τ (2 * k + 3) hn (by omega) =
      Spec.map (CommRingCat.ofHom
        (algebraMap Q (Q ⊗[R] WeierstrassIntegralChart.Coordinate W 1))) := by
  rw [arithmeticFactorRatioTensorInfinityMap, Category.assoc,
    arithmeticFactorRatioInfinityPolygonMap_structure, ← arithmeticInfinityTensorIso_structure,
    Iso.inv_hom_id_assoc]

end FLT.Mazur.WeierstrassDividedDepth
