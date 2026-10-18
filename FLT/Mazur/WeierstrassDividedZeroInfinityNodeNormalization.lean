/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroDiagonalFactorRatioOverlap

/-!
# Whole initial nodes normalized at the full infinity edge

Undo the accumulated initial node factors on the whole node, retaining the
original smoothing. The two full D(q) restrictions then use exactly reciprocal
parameters. The retained-side error is kept separately, without reduction.
-/

@[expose] public noncomputable section
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

/-- Normalize the entire initial node, with its complete original smoothing. -/
def arithmeticZeroInfinityNormalizedInitial (b : Bool) :
    A (.initial b) ⟶ PolygonSmoothing.chart Q τ := F b ≫ (T b).inv

local notation "f" => arithmeticZeroInfinityNormalizedInitial hπ data H m hj u hu

omit [IsBezout R] in
/-- The full source open has exactly the original factor-ratio coordinates after normalization. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedInitial_transport (b : Bool) :
    (E b).hom ≫ f b = N := by
  rw [arithmeticZeroInfinityNormalizedInitial, ← Category.assoc,
    arithmeticZeroDiagonalInitialFactorRatio_transport, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- The normalization is a whole-node isomorphism following the original full open embedding. -/
instance arithmeticZeroInfinityNormalizedInitial_isOpenImmersion (b : Bool) :
    IsOpenImmersion (f b) := by
  unfold arithmeticZeroInfinityNormalizedInitial
  infer_instance

/-- Both original orientations of the complete infinity chart enter the normalized node. -/
def arithmeticZeroInfinityNormalizedBoundary (b : Bool) :
    A .infinity ⟶ PolygonSmoothing.chart Q τ :=
  (V).hom ≫ (if b then (edgeInversion Q).hom else 𝟙 _) ≫ rightBranchOpen Q τ

local notation "g" => arithmeticZeroInfinityNormalizedBoundary hπ data H m hj u hu

instance arithmeticZeroInfinityNormalizedBoundary_isOpenImmersion (b : Bool) :
    IsOpenImmersion (g b) := by
  unfold arithmeticZeroInfinityNormalizedBoundary
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, Category.id_comp] <;> infer_instance

omit [IsBezout R] in
/-- The first complete original overlap has its unreduced factor-ratio parameter. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedInitial_overlap_first :
    l false ≫ f false = P ≫ rightBranchOpen Q τ := by
  simp only [arithmeticZeroInfinityNormalizedInitial,
    arithmeticZeroDiagonalInitialFactorRatio, arithmeticZeroDiagonalInitialOverlap,
    arithmeticZeroDiagonalInitialOpenIso, Bool.false_eq_true, ↓reduceIte,
    Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  exact arithmeticInitialFactorRatioChart_overlap_first π m W (π ^ 1)
    (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)

omit [IsBezout R] in
/-- The opposite complete overlap retains exactly the reciprocal full parameter. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedInitial_overlap_opposite :
    l true ≫ f true = P ≫ (edgeInversion Q).hom ≫ rightBranchOpen Q τ := by
  simp only [arithmeticZeroInfinityNormalizedInitial,
    arithmeticZeroDiagonalInitialFactorRatio, arithmeticZeroDiagonalInitialOverlap,
    arithmeticZeroDiagonalInitialOpenIso, ↓reduceIte,
    Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  exact arithmeticInitialFactorRatioChart_overlap_opposite π m W (π ^ 1)
    (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)

/-- Both complete original initial/infinity equations now hold inside their whole nodes. -/
@[reassoc] theorem arithmeticZeroInfinityNormalized_compatible (b : Bool) :
    i ≫ g b = l b ≫ f b := by
  rw [arithmeticZeroInfinityNormalizedBoundary, ← Category.assoc,
    arithmeticZeroDiagonalInfinityParameterIso_overlap]
  cases b
  · rw [arithmeticZeroInfinityNormalizedInitial_overlap_first]
    simp only [Bool.false_eq_true, ↓reduceIte, Category.id_comp]
  · rw [arithmeticZeroInfinityNormalizedInitial_overlap_opposite]
    simp only [↓reduceIte]

end FLT.Mazur.WeierstrassDividedDepth
