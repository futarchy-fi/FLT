/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOneInfinityNormalizedFullUnion
public import FLT.Mazur.WeierstrassDividedRevisedInitialBase
public import FLT.Mazur.WeierstrassDividedZeroDiagonalComparisonBase

/-!
# The full depth-one normalized nodes over the original coefficient base

Both entire initial opens and the original infinity cubic retain the global
coefficient projection. Their complete glued node comparisons preserve it.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticOneFiniteInitialIso arithmeticInitialFactorRatioChart arithmeticOneFiniteAtlasIso
  simultaneousTwistedArithmeticIso arithmeticLabeledAtlasMap
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 2 ≤ n)
  (u : Rˣ) (hu : (data ⟨2, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "G" => simultaneousTwistedArithmeticIso hπ data H m 1 hj u hu
local notation "E" => arithmeticOneFiniteAtlasIso hπ data H m m hj u hu
local notation "c" => arithmeticOneFiniteAtlasChart hπ data H m m hj u hu
local notation "I" => arithmeticOneDiagonalInitialTotalOpenIso hπ data H m hj u hu
local notation "J" => arithmeticOneDiagonalInfinityOpenIso hπ data H m hj u hu
local notation "V" => arithmeticOneDiagonalInfinityParameterIso hπ data H m hj u hu
local notation "f" => arithmeticOneInfinityNormalizedInitial hπ data H m hj u hu
local notation "g" => arithmeticOneInfinityNormalizedBoundary hπ data H m hj u hu
local notation "e" => arithmeticOneInfinityNormalizedNodeIso hπ data H m hj u hu
local notation "j" => arithmeticOneInfinityNormalizedToGlobal hπ data H m hj u hu

/-- The whole depth-one source retains the coefficient map of the actual arithmetic stage. -/
def arithmeticOneDiagonalSourceToBase :
    simultaneousTwistedArithmeticStage hπ data H m 1 hj u hu ⟶ Spec (.of Q) :=
  (G).inv ≫ finiteGlobalArithmeticStructure hπ data 2 hj m

local notation "q" => arithmeticOneDiagonalSourceToBase hπ data H m hj u hu

/-- Every full depth-one atlas comparison preserves the original coefficient projection. -/
@[reassoc] theorem arithmeticOneDiagonalFullAtlasIso_base (a : ArithmeticChartLabel 2) :
    (E a).hom ≫ c a ≫ q = arithmeticLabeledAtlasMap hπ data H m 2 hj a ≫
      finiteGlobalArithmeticStructure hπ data 2 hj m := by
  rw [← Category.assoc, ← arithmeticOneFiniteAtlasIso_chart,
    arithmeticOneDiagonalSourceToBase, Category.assoc, Iso.hom_inv_id_assoc]

/-- Both entire original initial opens lie over their actual global coefficient base. -/
@[reassoc] theorem arithmeticOneInfinityNormalizedInitial_base (b : Bool) :
    f b ≫ chartStructure Q τ = c (.initial b) ≫ q := by
  apply (cancel_epi (I b).hom).mp
  rw [arithmeticOneInfinityNormalizedInitial_transport_assoc]
  rw [PolygonSmoothing.chartStructure, arithmeticInitialFactorRatioChart_structure]
  change _ = (arithmeticOneFiniteInitialTotalOpenIso hπ data H m hj u hu m b).hom ≫ _
  rw [arithmeticOneFiniteInitialTotalOpenIso_atlas, arithmeticOneDiagonalFullAtlasIso_base]
  rw [arithmeticLabeledAtlasMap]
  exact (arithmeticLabeledInitialChart_base data H m 1 hj hπ b).symm

/-- The entire infinity parameter retains its original arithmetic coefficient projection. -/
@[reassoc] theorem arithmeticOneInfinityNormalizedParameter_base :
    (V).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Q Q[T;T⁻¹])) = c .infinity ≫ q := by
  apply (cancel_epi (J).hom).mp
  simp only [arithmeticOneDiagonalInfinityParameterIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.hom_inv_id_assoc, infinityFactorRatioIso_hom]
  simp only [arithmeticOneDiagonalInfinityOpenIso, Iso.trans_hom, Category.assoc,
    arithmeticOneDiagonalFullAtlasIso_base]
  rw [arithmeticLabeledAtlasMap, arithmeticTensorAtlas_infinity_structure,
    arithmeticInfinityTensorIso_structure]
  exact arithmeticFullInfinityRatioParameter_base π m W (π ^ 1)
    (Data.b3 (data ⟨0, by omega⟩)) (Data.b4 (data ⟨0, by omega⟩))
    (Data.b6 (data ⟨0, by omega⟩)) H.a1_unit H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
    (H.a3_div data) (H.a4_div data) (H.a6_div data)

/-- Both reciprocal infinity orientations retain the same full coefficient base. -/
@[reassoc] theorem arithmeticOneInfinityNormalizedBoundary_base (b : Bool) :
    g b ≫ chartStructure Q τ = c .infinity ≫ q := by
  cases b <;>
    simp only [arithmeticOneInfinityNormalizedBoundary, Bool.false_eq_true, ↓reduceIte,
      Category.id_comp, Category.assoc, rightBranchOpen_base, edgeInversion_base,
      arithmeticOneInfinityNormalizedParameter_base]

/-- Each full source-node comparison is over the actual global arithmetic coefficient map. -/
@[reassoc] theorem arithmeticOneInfinityNormalizedNodeIso_base (b : Bool) :
    (e b).hom ≫ chartStructure Q τ = j b ≫ q := by
  apply Limits.pushout.hom_ext
  · rw [arithmeticOneInfinityNormalizedNodeIso_infinity_assoc,
      arithmeticOneInfinityNormalizedToGlobal_infinity_assoc,
      arithmeticOneInfinityNormalizedBoundary_base]
  · rw [arithmeticOneInfinityNormalizedNodeIso_initial_assoc,
      arithmeticOneInfinityNormalizedToGlobal_initial_assoc,
      arithmeticOneInfinityNormalizedInitial_base]

end FLT.Mazur.WeierstrassDividedDepth
