/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroInitialTotalBase
public import FLT.Mazur.WeierstrassDividedZeroDiagonalInfinityComparisonRestriction
public import FLT.Mazur.WeierstrassDividedRevisedInitialBase
public import FLT.Mazur.WeierstrassDividedZeroDiagonalFirstInfinityIso

/-!
# The full diagonal initial and infinity comparisons preserve the original base

The source structure is the original global coefficient map carried through
its actual global isomorphism. Both full comparisons recover this structure.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFiniteInitialIso arithmeticInitialFactorRatioChart
  arithmeticZeroFiniteAtlasIso arithmeticZeroFiniteAtlasChart
  simultaneousTwistedArithmeticIso arithmeticLabeledAtlasMap
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "G" => simultaneousTwistedArithmeticIso hπ data H m 0 hj u hu
local notation "E" => arithmeticZeroFiniteAtlasIso hπ data H m m hj u hu
local notation "c" => arithmeticZeroFiniteAtlasChart hπ data H m m hj u hu
local notation "p" => arithmeticZeroDiagonalPolygonToBase hπ data H m hj u hu
local notation "I" => arithmeticZeroDiagonalInitialOpenIso hπ data H m hj u hu
local notation "J" => arithmeticZeroDiagonalInfinityOpenIso hπ data H m hj u hu
local notation "f" => arithmeticZeroDiagonalFactorRatioInitialMap hπ data H m hj u hu
local notation "g" => arithmeticZeroDiagonalFactorRatioInfinityMap hπ data H m hj u hu

/-- The corrected global source keeps its original full arithmetic coefficient map. -/
def arithmeticZeroDiagonalSourceToBase :
    simultaneousTwistedArithmeticStage hπ data H m 0 hj u hu ⟶ Spec (.of Q) :=
  (G).inv ≫ finiteGlobalArithmeticStructure hπ data 1 hj m

local notation "q" => arithmeticZeroDiagonalSourceToBase hπ data H m hj u hu

/-- Every whole source chart has exactly the original global coefficient structure. -/
@[reassoc] theorem arithmeticZeroDiagonalFullAtlasIso_base (a : ArithmeticChartLabel 1) :
    (E a).hom ≫ c a ≫ q = arithmeticLabeledAtlasMap hπ data H m 1 hj a ≫
      finiteGlobalArithmeticStructure hπ data 1 hj m := by
  rw [← Category.assoc, ← arithmeticZeroFiniteAtlasIso_chart,
    arithmeticZeroDiagonalSourceToBase, Category.assoc, Iso.hom_inv_id_assoc]

omit [IsBezout R] in
/-- The full original polynomial factor ratio retains every coefficient after correction. -/
@[reassoc] theorem arithmeticZeroDiagonalFactorRatioInitialMap_original_base (b : Bool) :
    (I b).hom ≫ f b ≫ p = Spec.map (CommRingCat.ofHom
      (algebraMap Q (PolynomialNodeOpen (W.map (algebraMap R Q))
        (algebraMap R Q (π ^ 1))))) := by
  rw [arithmeticZeroDiagonalFactorRatioInitialMap_transport_assoc,
    arithmeticZeroDiagonalPolygonInitialMap_base,
    arithmeticZeroDiagonalInitialTotalNodeIso_base]
  exact arithmeticInitialFactorRatioChart_structure ..

/-- Both whole corrected initial opens have their actual original global arithmetic base. -/
@[reassoc] theorem arithmeticZeroDiagonalFactorRatioInitialMap_base (b : Bool) :
    f b ≫ p = c (.initial b) ≫ q := by
  apply (cancel_epi (I b).hom).mp
  rw [arithmeticZeroDiagonalFactorRatioInitialMap_original_base]
  change _ = (E (.initial b)).hom ≫ c (.initial b) ≫ q
  rw [arithmeticZeroDiagonalFullAtlasIso_base]
  rw [arithmeticLabeledAtlasMap]
  exact (arithmeticLabeledInitialChart_base data H m 0 hj hπ b).symm

omit [IsBezout R] in
/-- The full original infinity cubic retains every coefficient after node transport. -/
@[reassoc] theorem arithmeticZeroDiagonalFactorRatioInfinityMap_original_base :
    (J).hom ≫ g ≫ p = WeierstrassIntegralChart.chartStructure
      (W.map (algebraMap R Q)) 1 := by
  simp only [arithmeticZeroDiagonalFactorRatioInfinityMap,
    arithmeticZeroDiagonalInitialInfinityBoundary, Category.assoc,
    arithmeticZeroDiagonalPolygonInitialMap_base,
    arithmeticZeroDiagonalInitialTotalNodeIso_base, rightBranchOpen_base,
    arithmeticZeroDiagonalInfinityParameterIso, Iso.trans_hom, Iso.symm_hom,
    Iso.hom_inv_id_assoc, infinityFactorRatioIso_hom]
  exact arithmeticFullInfinityRatioParameter_base π m W (π ^ 1)
    (Data.b3 (data ⟨0, by omega⟩)) (Data.b4 (data ⟨0, by omega⟩))
    (Data.b6 (data ⟨0, by omega⟩)) H.a1_unit H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
    (H.a3_div data) (H.a4_div data) (H.a6_div data)

/-- The whole actual infinity map lies over the original global arithmetic coefficient map. -/
@[reassoc] theorem arithmeticZeroDiagonalFactorRatioInfinityMap_base :
    g ≫ p = c .infinity ≫ q := by
  apply (cancel_epi (J).hom).mp
  rw [arithmeticZeroDiagonalFactorRatioInfinityMap_original_base]
  simp only [arithmeticZeroDiagonalInfinityOpenIso, Iso.trans_hom, Category.assoc,
    arithmeticZeroDiagonalFullAtlasIso_base]
  rw [arithmeticLabeledAtlasMap, arithmeticTensorAtlas_infinity_structure,
    arithmeticInfinityTensorIso_structure]

/-- The entire glued first node preserves the actual global source coefficient base. -/
@[reassoc] theorem arithmeticZeroDiagonalFirstInfinityNodeMap_base :
    arithmeticZeroDiagonalFirstInfinityNodeMap hπ data H m hj u hu ≫
      arithmeticZeroDiagonalPolygonInitialMap hπ data H m hj u hu false ≫ p =
      arithmeticZeroDiagonalFirstInfinityToGlobal hπ data H m hj u hu ≫ q := by
  apply pushout.hom_ext
  · rw [arithmeticZeroDiagonalFirstInfinityNodeMap_infinity_polygon_assoc,
      arithmeticZeroDiagonalFirstInfinityToGlobal_infinity_assoc,
      arithmeticZeroDiagonalFactorRatioInfinityMap_base]
  · rw [arithmeticZeroDiagonalFirstInfinityNodeMap_initial_polygon_assoc,
      arithmeticZeroDiagonalFirstInfinityToGlobal_initial_assoc,
      arithmeticZeroDiagonalFactorRatioInitialMap_base]

/-- The full actual first source-union comparison lies over its original arithmetic base. -/
@[reassoc] theorem arithmeticZeroDiagonalFirstInfinityUnionComparison_base :
    arithmeticZeroDiagonalFirstInfinityUnionComparison hπ data H m hj u hu ≫ p =
      (arithmeticZeroDiagonalFirstInfinityUnion hπ data H m hj u hu).ι ≫ q := by
  apply (cancel_epi (arithmeticZeroDiagonalFirstInfinityUnionIso hπ data H m hj u hu).hom).mp
  simp only [arithmeticZeroDiagonalFirstInfinityUnionComparison, Category.assoc,
    arithmeticZeroDiagonalFirstInfinityUnionNodeMap_transport_assoc,
    arithmeticZeroDiagonalFirstInfinityNodeMap_base,
    arithmeticZeroDiagonalFirstInfinityUnionIso_global_assoc]

end FLT.Mazur.WeierstrassDividedDepth
