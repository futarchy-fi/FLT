/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroDiagonalFactorRatioInfinity
public import FLT.Mazur.WeierstrassDividedZeroDiagonalAtlasRestriction
public import FLT.Mazur.WeierstrassDividedArithmeticInfinityFactorRatioTensorRestriction
public import FLT.Mazur.WeierstrassDividedArithmeticInfinityParameterRestriction

/-!
# The complete diagonal infinity parameter follows the original quotient

The full corrected atlas isomorphism preserves the original quotient square.
Apply it to the unchanged infinity tensor chart and its canonical Laurent ratio.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
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
local notation "E" => fun k ↦ arithmeticZeroFiniteAtlasIso hπ data H k k hj u hu
local notation "S" => arithmeticZeroDiagonalAtlasRestriction hπ data H hj u hu m
local notation "c" => fun k ↦ arithmeticZeroDiagonalAtlasChart hπ data H k hj u hu
local notation "G" => fun k ↦ simultaneousTwistedArithmeticIso hπ data H k 0 hj u hu
local notation "I" => fun k ↦ arithmeticZeroDiagonalInfinityOpenIso hπ data H k hj u hu
local notation "P" => fun k ↦ arithmeticZeroDiagonalInfinityParameterIso hπ data H k hj u hu

/-- All complete chart corrections preserve the original arithmetic quotient square. -/
@[reassoc] theorem arithmeticZeroDiagonalFullAtlasIso_restriction
    (a : ArithmeticChartLabel 1) :
    (E m a).hom ≫ S a = arithmeticLabeledAtlasRestriction hπ data H m 1 hj a ≫
      (E (m + 1) a).hom := by
  apply (cancel_mono (c (m + 1) a)).mp
  rw [Category.assoc, arithmeticZeroDiagonalAtlasChart_restriction]
  simp only [arithmeticZeroDiagonalAtlasChart, Category.assoc]
  rw [← Category.assoc, ← arithmeticZeroFiniteAtlasIso_chart,
    ← arithmeticZeroFiniteAtlasIso_chart, Category.assoc,
    simultaneousTwistedArithmeticIso_restriction,
    ← Category.assoc, arithmeticLabeledAtlasMap_restriction_assoc, Category.assoc]

/-- The whole original cubic comparison follows the actual diagonal infinity quotient. -/
@[reassoc] theorem arithmeticZeroDiagonalInfinityOpenIso_restriction :
    (I m).hom ≫ S .infinity =
      arithmeticChartRestriction R π m W 1 ≫ (I (m + 1)).hom := by
  simp only [arithmeticZeroDiagonalInfinityOpenIso, Iso.trans_hom, Category.assoc,
    arithmeticZeroDiagonalFullAtlasIso_restriction]
  rw [arithmeticLabeledAtlasRestriction, ← arithmeticInfinityTensorIso_restriction_assoc]

/-- The full diagonal infinity parameter keeps every original Laurent quotient function. -/
@[reassoc] theorem arithmeticZeroDiagonalInfinityParameterIso_restriction :
    S .infinity ≫ (P (m + 1)).hom =
      (P m).hom ≫ closingOverlapRestriction (R := R) (π := π) m := by
  apply (cancel_epi (I m).hom).mp
  rw [← Category.assoc, arithmeticZeroDiagonalInfinityOpenIso_restriction]
  simp only [arithmeticZeroDiagonalInfinityParameterIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.hom_inv_id_assoc, infinityFactorRatioIso_hom]
  exact arithmeticFullInfinityRatioParameter_restriction π m W (π ^ 1)
    (Data.b3 (data ⟨0, by omega⟩)) (Data.b4 (data ⟨0, by omega⟩))
    (Data.b6 (data ⟨0, by omega⟩)) H.a1_unit H.scale_div H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
    (H.a3_div data) (H.a4_div data) (H.a6_div data)

end FLT.Mazur.WeierstrassDividedDepth
