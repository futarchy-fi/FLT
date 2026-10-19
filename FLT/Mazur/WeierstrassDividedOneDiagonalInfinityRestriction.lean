/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOneDiagonalInfinityParameter
public import FLT.Mazur.WeierstrassDividedOneDiagonalAtlasRestriction
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
  arithmeticOneFiniteInitialIso arithmeticInitialFactorRatioChart
  arithmeticOneFiniteAtlasIso arithmeticOneFiniteAtlasChart
  simultaneousTwistedArithmeticIso arithmeticLabeledAtlasMap
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 2 ≤ n)
  (u : Rˣ) (hu : (data ⟨2, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "E" => fun k ↦ arithmeticOneFiniteAtlasIso hπ data H k k hj u hu
local notation "S" => arithmeticOneDiagonalAtlasRestriction hπ data H hj u hu m
local notation "c" => fun k ↦ arithmeticOneDiagonalAtlasChart hπ data H k hj u hu
local notation "G" => fun k ↦ simultaneousTwistedArithmeticIso hπ data H k 1 hj u hu
local notation "I" => fun k ↦ arithmeticOneDiagonalInfinityOpenIso hπ data H k hj u hu
local notation "P" => fun k ↦ arithmeticOneDiagonalInfinityParameterIso hπ data H k hj u hu

/-- All complete chart corrections preserve the original arithmetic quotient square. -/
@[reassoc] theorem arithmeticOneDiagonalFullAtlasIso_restriction
    (a : ArithmeticChartLabel 2) :
    (E m a).hom ≫ S a = arithmeticLabeledAtlasRestriction hπ data H m 2 hj a ≫
      (E (m + 1) a).hom := by
  apply (cancel_mono (c (m + 1) a)).mp
  rw [Category.assoc, arithmeticOneDiagonalAtlasChart_restriction]
  simp only [arithmeticOneDiagonalAtlasChart, Category.assoc]
  rw [← Category.assoc, ← arithmeticOneFiniteAtlasIso_chart,
    ← arithmeticOneFiniteAtlasIso_chart, Category.assoc,
    simultaneousTwistedArithmeticIso_restriction,
    ← Category.assoc, arithmeticLabeledAtlasMap_restriction_assoc, Category.assoc]

/-- The whole original cubic comparison follows the actual diagonal infinity quotient. -/
@[reassoc] theorem arithmeticOneDiagonalInfinityOpenIso_restriction :
    (I m).hom ≫ S .infinity =
      arithmeticChartRestriction R π m W 1 ≫ (I (m + 1)).hom := by
  simp only [arithmeticOneDiagonalInfinityOpenIso, Iso.trans_hom, Category.assoc,
    arithmeticOneDiagonalFullAtlasIso_restriction]
  rw [arithmeticLabeledAtlasRestriction, ← arithmeticInfinityTensorIso_restriction_assoc]

/-- The full diagonal infinity parameter keeps every original Laurent quotient function. -/
@[reassoc] theorem arithmeticOneDiagonalInfinityParameterIso_restriction :
    S .infinity ≫ (P (m + 1)).hom =
      (P m).hom ≫ closingOverlapRestriction (R := R) (π := π) m := by
  apply (cancel_epi (I m).hom).mp
  rw [← Category.assoc, arithmeticOneDiagonalInfinityOpenIso_restriction]
  simp only [arithmeticOneDiagonalInfinityParameterIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.hom_inv_id_assoc, infinityFactorRatioIso_hom]
  exact arithmeticFullInfinityRatioParameter_restriction π m W (π ^ 1)
    (Data.b3 (data ⟨0, by omega⟩)) (Data.b4 (data ⟨0, by omega⟩))
    (Data.b6 (data ⟨0, by omega⟩)) H.a1_unit H.scale_div H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
    (H.a3_div data) (H.a4_div data) (H.a6_div data)

end FLT.Mazur.WeierstrassDividedDepth
