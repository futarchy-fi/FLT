/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRevisedInfinityMap

/-!
# Full original tensor charts in the revised polygon

The original affine and cubic coefficient isomorphisms transport both maps.
Their whole original infinity overlap retains the same projective transition.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] arithmeticOriginalRevisedAffineMap
  arithmeticOriginalRevisedInfinityMap arithmeticInitialNodeChart arithmeticOppositeInitialNodeChart
variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R} {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "q" => algebraMap R Q
local notation "d₀" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "b3" => Data.b3 d₀
local notation "b4" => Data.b4 d₀
local notation "b6" => Data.b6 d₀
local notation "e" => arithmeticInitialTensorIso π m W (π ^ 1) b3 b4 b6
local notation "e∞" => arithmeticInfinityTensorIso π m W
local notation "Y" => arithmeticRevisedPolygon data H m j hj u hu

/-- The full original affine tensor chart retains its constructed revised comparison. -/
def arithmeticOriginalRevisedTensorAffineMap :
    Spec (.of (Q ⊗[R] Coordinate W (π ^ 1) b3 b4 b6)) ⟶ Y :=
  (e).inv ≫ arithmeticOriginalRevisedAffineMap data H m j hj u hu

/-- The full original infinity tensor chart retains the complete regular factor ratio. -/
def arithmeticOriginalRevisedTensorInfinityMap :
    Spec (.of (Q ⊗[R] WeierstrassIntegralChart.Coordinate W 1)) ⟶ Y :=
  (e∞).inv ≫ arithmeticOriginalRevisedInfinityMap data H m j hj u hu

/-- Tensor transport recovers every function of the original full affine chart. -/
@[reassoc] theorem arithmeticOriginalRevisedTensorAffineMap_transport :
    (e).hom ≫ arithmeticOriginalRevisedTensorAffineMap data H m j hj u hu =
      arithmeticOriginalRevisedAffineMap data H m j hj u hu := by
  rw [arithmeticOriginalRevisedTensorAffineMap, Iso.hom_inv_id_assoc]

/-- Tensor transport also recovers every function on the original full infinity chart. -/
@[reassoc] theorem arithmeticOriginalRevisedTensorInfinityMap_transport :
    (e∞).hom ≫ arithmeticOriginalRevisedTensorInfinityMap data H m j hj u hu =
      arithmeticOriginalRevisedInfinityMap data H m j hj u hu := by
  rw [arithmeticOriginalRevisedTensorInfinityMap, Iso.hom_inv_id_assoc]

/-- The actual tensor node inclusions recover both full revised initial maps. -/
@[reassoc] theorem arithmeticOriginalRevisedTensorAffineMap_chart (b : Bool) :
    (if b then arithmeticOppositeInitialTensorNodeChart π m W (π ^ 1) b3 b4 b6 H.a1_unit
      H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _)
      else arithmeticInitialTensorNodeChart π m W (π ^ 1) b3 b4 b6 H.a1_unit
        H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _)) ≫
        arithmeticOriginalRevisedTensorAffineMap data H m j hj u hu =
      arithmeticOriginalRevisedInitialMap data H m j hj u hu b := by
  have h := arithmeticOriginalRevisedAffineMap_chart data H m j hj u hu b
  cases b <;> simpa only [Bool.false_eq_true, ↓reduceIte,
    arithmeticInitialTensorNodeChart, arithmeticOppositeInitialTensorNodeChart,
    Category.assoc, arithmeticOriginalRevisedTensorAffineMap_transport] using h

attribute [local irreducible] polynomialSlopeRoot
  polynomialNodeOverlapInfinityIso

/-- The original full infinity overlap agrees with the revised first initial map. -/
@[reassoc] theorem arithmeticOriginalRevisedTensorInfinityMap_overlap :
    arithmeticFactorRatioOverlapInfinity π m W (π ^ 1) b3 b4 b6 H.a1_unit H.a2_div
        (H.b3_div _) (H.b4_div _) (H.b6_div _)
        (Data.factor3 d₀) (Data.factor4 d₀) (Data.factor6 d₀) ≫
      arithmeticOriginalRevisedTensorInfinityMap data H m j hj u hu =
        polynomialNodeOverlapInclusion (W.map q) (q (π ^ 1)) ≫
          arithmeticOriginalRevisedInitialMap data H m j hj u hu false := by
  rw [arithmeticFactorRatioOverlapInfinity, Category.assoc, Category.assoc,
    arithmeticOriginalRevisedTensorInfinityMap_transport,
    arithmeticOriginalRevisedInfinityMap_initial,
    ← Category.assoc, polynomialNodeOverlapInfinityIso_hom_inclusion, Category.assoc]
  apply congrArg (fun f ↦ polynomialNodeOverlapInclusion (W.map q) (q (π ^ 1)) ≫ f)
  simpa only [Bool.false_eq_true, ↓reduceIte, arithmeticInitialNodeChart] using
    arithmeticOriginalRevisedAffineMap_chart data H m j hj u hu false

end FLT.Mazur.WeierstrassDividedDepth
