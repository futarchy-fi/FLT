/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRevisedTensorMaps
public import FLT.Mazur.WeierstrassDividedRevisedTargetBase
public import FLT.Mazur.WeierstrassDividedArithmeticTensorProjection

/-!
# Base compatibility on the entire original infinity tensor chart

The regular infinity factor ratio and the tensor comparison preserve the
coefficient projection without restricting the original cubic chart.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R} {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "B" => arithmeticRevisedPolygonToBase data H m j hj u hu

/-- The full original infinity factor ratio retains the specialized cubic's base. -/
@[reassoc] theorem arithmeticOriginalRevisedInfinityMap_base :
    arithmeticOriginalRevisedInfinityMap data H m j hj u hu ≫ B =
      WeierstrassIntegralChart.chartStructure (W.map (algebraMap R Q)) 1 := by
  unfold arithmeticOriginalRevisedInfinityMap factorRatioInfinityTargetMap
  rw [Category.assoc, Category.assoc, arithmeticRevisedPolygonInitialChart_base,
    rightBranchOpen_base]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (LaurentUnitPoints.evalUnit _).commutes

/-- The entire original tensor infinity map preserves the quotient coefficients. -/
@[reassoc] theorem arithmeticOriginalRevisedTensorInfinityMap_base :
    arithmeticOriginalRevisedTensorInfinityMap data H m j hj u hu ≫ B =
      Spec.map (CommRingCat.ofHom
        (algebraMap Q (Q ⊗[R] WeierstrassIntegralChart.Coordinate W 1))) := by
  rw [arithmeticOriginalRevisedTensorInfinityMap, Category.assoc,
    arithmeticOriginalRevisedInfinityMap_base, ← arithmeticInfinityTensorIso_structure,
    Iso.inv_hom_id_assoc]

end FLT.Mazur.WeierstrassDividedDepth
