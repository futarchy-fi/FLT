/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroInfinityNormalizedRetained
public import FLT.Mazur.WeierstrassDividedZeroDiagonalComparisonBase

/-!
# Original coefficient bases on both whole normalized nodes

Undoing the accumulated node factors preserves the original coefficient map.
Both full source unions, including the opposite infinity orientation, lie over it.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFiniteInitialIso arithmeticInitialFactorRatioChart arithmeticZeroFiniteAtlasIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "N" => arithmeticInitialFactorRatioChart π m W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "P" => arithmeticFactorRatioOverlapParameter π m W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "E" => arithmeticZeroDiagonalInitialOpenIso hπ data H m hj u hu
local notation "T" => arithmeticZeroDiagonalInitialTotalNodeIso hπ data H m hj u hu
local notation "F" => arithmeticZeroDiagonalInitialFactorRatio hπ data H m hj u hu
local notation "l" => arithmeticZeroDiagonalInitialOverlap hπ data H m hj u hu
local notation "i" => arithmeticZeroDiagonalOverlapToInfinity hπ data H m hj u hu
local notation "V" => arithmeticZeroDiagonalInfinityParameterIso hπ data H m hj u hu
local notation "A" => arithmeticZeroFiniteAtlasObject hπ data H m m hj u hu

local notation "f" => arithmeticZeroInfinityNormalizedInitial hπ data H m hj u hu
local notation "A₀" => arithmeticZeroFiniteInitialTotalPunctureIso hπ data H m hj u hu m
local notation "P₀" => arithmeticZeroFiniteInitialPuncture hπ data H m m 0 hj u hu
local notation "M" => arithmeticInitialMobiusParameter π m W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.scale_div H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "L" => arithmeticFactorRatioLaurentIso π m W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.scale_div H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "D" => arithmeticZeroDiagonalState hπ data H 0 hj u hu
local notation "s" => PolygonArithmeticSimultaneous.State.initial D m

local notation "c" => arithmeticZeroFiniteAtlasChart hπ data H m m hj u hu
local notation "q" => arithmeticZeroDiagonalSourceToBase hπ data H m hj u hu
local notation "g" => arithmeticZeroInfinityNormalizedBoundary hπ data H m hj u hu
local notation "e" => arithmeticZeroInfinityNormalizedNodeIso hπ data H m hj u hu
local notation "j" => arithmeticZeroInfinityNormalizedToGlobal hπ data H m hj u hu

omit [IsBezout R] in
/-- Undoing the full accumulated correction preserves the entire quotient coefficient ring. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedNode_base (b : Bool) :
    (T b).inv ≫ chartStructure Q τ = chartStructure Q (s b) := by
  rw [← arithmeticZeroDiagonalInitialTotalNodeIso_base hπ data H m hj u hu b,
    Iso.inv_hom_id_assoc]

/-- Both original full initial opens keep their actual global coefficient projection. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedInitial_base (b : Bool) :
    f b ≫ chartStructure Q τ = c (.initial b) ≫ q := by
  rw [arithmeticZeroInfinityNormalizedInitial, Category.assoc,
    arithmeticZeroInfinityNormalizedNode_base]
  have h := arithmeticZeroDiagonalFactorRatioInitialMap_base hπ data H m hj u hu b
  simpa only [arithmeticZeroDiagonalFactorRatioInitialMap, Category.assoc,
    arithmeticZeroDiagonalPolygonInitialMap_base] using h

/-- The entire original infinity parameter lies over the original global base. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedParameter_base :
    (V).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Q Q[T;T⁻¹])) = c .infinity ≫ q := by
  have h := arithmeticZeroDiagonalFactorRatioInfinityMap_base hπ data H m hj u hu
  simpa only [arithmeticZeroDiagonalFactorRatioInfinityMap,
    arithmeticZeroDiagonalInitialInfinityBoundary, Category.assoc,
    arithmeticZeroDiagonalPolygonInitialMap_base,
    arithmeticZeroDiagonalInitialTotalNodeIso_base, rightBranchOpen_base] using h

/-- Reciprocal orientation does not change the full infinity coefficient projection. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedBoundary_base (b : Bool) :
    g b ≫ chartStructure Q τ = c .infinity ≫ q := by
  cases b <;>
    simp only [arithmeticZeroInfinityNormalizedBoundary, Bool.false_eq_true, ↓reduceIte,
      Category.id_comp, Category.assoc, rightBranchOpen_base, edgeInversion_base,
      arithmeticZeroInfinityNormalizedParameter_base]

/-- Each complete source node comparison is over the actual global arithmetic base. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedNodeIso_base (b : Bool) :
    (e b).hom ≫ chartStructure Q τ = j b ≫ q := by
  apply Limits.pushout.hom_ext
  · rw [arithmeticZeroInfinityNormalizedNodeIso_infinity_assoc,
      arithmeticZeroInfinityNormalizedToGlobal_infinity_assoc,
      arithmeticZeroInfinityNormalizedBoundary_base]
  · rw [arithmeticZeroInfinityNormalizedNodeIso_initial_assoc,
      arithmeticZeroInfinityNormalizedToGlobal_initial_assoc,
      arithmeticZeroInfinityNormalizedInitial_base]

end FLT.Mazur.WeierstrassDividedDepth
