/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPolygonComparisonCharts
public import FLT.Mazur.WeierstrassDividedArithmeticInfinityFactorRatioTensorRestriction
public import FLT.Mazur.WeierstrassDividedArithmeticLabeledSystem

/-!
# All concrete polygon comparisons preserve arithmetic coefficients

The terminal square uses its full normalized smoothing. The retained squares
use the complete root corrections and depth recurrence. Initial and infinity
squares use the original tensor coefficient maps.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassModificationX WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "F" => fun m ↦ arithmeticPolygonComparisonChart hπ data H m j hj u hu
local notation "r" => fun m ↦ arithmeticLabeledAtlasRestriction hπ data H m (j + 1) hj
local notation "q" => fun m ↦ arithmeticFactorRatioPolygonRestriction π m W (π ^ 1)
  H.a1_unit H.scale_div (j + 1)
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))

omit [IsBezout R] in
/-- Every constructed full chart comparison commutes with the actual consecutive quotient map. -/
@[reassoc] theorem arithmeticPolygonComparisonChart_restriction
    (m : ℕ) (i : ArithmeticChartLabel (j + 1)) :
    r m i ≫ F (m + 1) i = F m i ≫ q m := by
  cases i with
  | infinity =>
    exact (arithmeticFactorRatioLabeledInfinityMap_restriction
      m (j + 1) data H hπ hj).symm
  | initial b =>
    exact (arithmeticFactorRatioLabeledInitialMap_restriction
      data H hπ m (j + 1) hj b).symm
  | retained a b =>
    exact (arithmeticStartOneRetainedMap_restriction hπ data H m (j + 1) hj a b).symm
  | terminal =>
    exact fixedTerminalPolygonMap_restriction π W (π ^ (1 + j + 1))
      (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit (H.scale (j + 1)) H.a2_div
      (H.b3_div _) (H.b4_div _) (H.b6_div _) u hu hπ m (j + 1) 0

/-- The prescribed normalized polygons with their actual quotient coefficient maps. -/
def arithmeticComparisonPolygonSystem : ℕ ⥤ Scheme := Functor.ofSequence q

/-- Each original labeled chart system maps naturally to the same polygon system. -/
def arithmeticPolygonComparisonChartSystem (i : ArithmeticChartLabel (j + 1)) :
    arithmeticLabeledChartSystem hπ data H (j + 1) hj i ⟶
      arithmeticComparisonPolygonSystem data H j :=
  NatTrans.ofSequence (fun m ↦ F m i) (by
    intro m
    simpa only [arithmeticLabeledChartSystem, arithmeticComparisonPolygonSystem,
      Functor.ofSequence_obj, Functor.ofSequence_map_homOfLE_succ] using
        arithmeticPolygonComparisonChart_restriction hπ data H j hj u hu m i)

omit [IsBezout R] in
/-- Nonadjacent arithmetic orders preserve every original full chart coefficient square. -/
@[reassoc] theorem arithmeticPolygonComparisonChartSystem_naturality
    (i : ArithmeticChartLabel (j + 1)) {a b : ℕ} (hab : a ≤ b) :
    (arithmeticLabeledChartSystem hπ data H (j + 1) hj i).map (homOfLE hab) ≫ F b i =
      F a i ≫ (arithmeticComparisonPolygonSystem data H j).map (homOfLE hab) :=
  (arithmeticPolygonComparisonChartSystem hπ data H j hj u hu i).naturality (homOfLE hab)

end FLT.Mazur.WeierstrassDividedDepth
