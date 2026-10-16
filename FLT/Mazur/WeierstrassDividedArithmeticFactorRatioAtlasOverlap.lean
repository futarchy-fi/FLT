/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticFactorRatioOverlap
public import FLT.Mazur.WeierstrassDividedArithmeticInitialTriangleCompatibility
public import FLT.Mazur.WeierstrassDividedArithmeticTensorProjection

/-!
# The full factor-ratio transition is the original arithmetic atlas transition

Equality is detected by the original coefficient and integral projections.
The comparison therefore retains the complete initial/infinity intersection
at every finite stage, without replacing the atlas or its overlap map.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassModificationX WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFactorRatioOverlapInfinity
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (H : ArithmeticAtlasCoefficients data) (m k : ℕ) (hk : k ≤ n)
local notation "Q" => Quotient R π m
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "P" => polynomialNodeOverlapInclusion
  (W.map (algebraMap R Q)) (algebraMap R Q (π ^ start))
local notation "F" => arithmeticInitialTensorNodeChart π m W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "I" => arithmeticInitialOverlapToInfinity hπ data m k hk
  H.a1_unit H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "c" => arithmeticTensorAtlasMap hπ data m k hk 0
local notation "a" => finiteArithmeticInitialTensorChart hπ data m k hk

/-- The original full atlas overlap retains its actual arithmetic coefficient projection. -/
@[reassoc] theorem arithmeticInitialOverlapToInfinity_structure :
    I ≫ Spec.map (CommRingCat.ofHom
      (algebraMap Q (Q ⊗[R] WeierstrassIntegralChart.Coordinate W 1))) =
      Spec.map (CommRingCat.ofHom (algebraMap Q
        (PolynomialNodeOverlap (W.map (algebraMap R Q)) (algebraMap R Q (π ^ start))))) := by
  rw [← arithmeticTensorAtlas_infinity_structure hπ data m k hk]
  have hi : I ≫ c = (P ≫ F) ≫ a :=
    arithmeticInitialOverlapToInfinity_comp hπ data m k hk
      H.a1_unit H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _)
  rw [← Category.assoc, hi, Category.assoc, finiteArithmeticInitialTensorChart_structure,
    Category.assoc, arithmeticInitialTensorNodeChart_structure]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1

/-- The original full atlas overlap retains the integral cubic contraction of its affine leg. -/
@[reassoc] theorem arithmeticInitialOverlapToInfinity_toCurve :
    I ≫ TensorOpenChart.projection ≫ integralCurveChart W 1 =
      P ≫ F ≫ TensorOpenChart.projection ≫
        WeierstrassModificationX.toCurve W (π ^ start) (Data.b3 d) (Data.b4 d) (Data.b6 d)
          (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) := by
  have hc : c ≫ finiteGlobalArithmeticProjection hπ data k hk m ≫
      finiteGlobalContraction hπ data k hk =
        TensorOpenChart.projection ≫ integralCurveChart W 1 := by
    rw [arithmeticTensorAtlas_infinity_projection_assoc, finiteInfinityChart_contraction]
  rw [← hc, ← Category.assoc]
  have hi : I ≫ c = (P ≫ F) ≫ a :=
    arithmeticInitialOverlapToInfinity_comp hπ data m k hk
      H.a1_unit H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _)
  rw [hi, Category.assoc, finiteArithmeticInitialTensorChart_projection_assoc,
    finiteLocalChart_contraction, finiteInitialChart_toCurve]
  simp only [Category.assoc]

/-- The explicit factor-ratio overlap is exactly the original full arithmetic atlas overlap. -/
theorem arithmeticFactorRatioOverlapInfinity_eq_atlas :
    arithmeticFactorRatioOverlapInfinity π m W (π ^ start)
      (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
        (H.b3_div _) (H.b4_div _) (H.b6_div _)
        (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) = I := by
  apply TensorOpenChart.spectrum_hom_ext
  · rw [arithmeticFactorRatioOverlapInfinity_structure,
      arithmeticInitialOverlapToInfinity_structure hπ data H m k hk]
  · apply (cancel_mono (integralCurveChart W 1)).mp
    rw [Category.assoc, Category.assoc, arithmeticFactorRatioOverlapInfinity_toCurve,
      arithmeticInitialOverlapToInfinity_toCurve hπ data H m k hk]

end FLT.Mazur.WeierstrassDividedDepth
