/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthClosingFactorBase
public import FLT.Mazur.WeierstrassDividedZeroDiagonalComparisonBase
public import FLT.Mazur.WeierstrassDividedOriginalNodeBase

/-!
# Full original bases before the depth-zero closing iterations

The entire original retained and terminal charts keep the coefficient map of
the actual global source, through all four preliminary correction rounds.
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
local notation "q" => arithmeticZeroDiagonalSourceToBase hπ data H m hj u hu
local notation "S" => finiteGlobalArithmeticStructure hπ data 1 hj m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "c" => changedArithmeticAtlasChart hπ data H m 0 hj u hu
local notation "E" => changedArithmeticAtlasIso hπ data H m 0 hj u hu
local notation "ω" => arithmeticFourthOuterAtlasChart hπ data H m 0 hj u hu
local notation "N" => arithmeticFourthOuterLastIdentification hπ data H m 0 hj u hu

/-- The whole changed atlas retains the global source's original coefficient map. -/
@[reassoc] theorem changedArithmeticZeroAtlasIso_original_base (a : ArithmeticChartLabel 1) :
    (E a).hom ≫ c a ≫ q = arithmeticLabeledAtlasMap hπ data H m 1 hj a ≫ S := by
  rw [← Category.assoc, ← changedArithmeticAtlasIso_chart,
    arithmeticZeroDiagonalSourceToBase, Category.assoc, Iso.hom_inv_id_assoc]

/-- The original normalized retained chart has its full quotient coefficient projection. -/
@[reassoc] theorem changedArithmeticZeroAtlas_retained_base (b : Bool) :
    c (.retained ⟨0, by omega⟩ b) ≫ q = chartStructure Q τ := by
  apply (cancel_epi (E (.retained ⟨0, by omega⟩ b)).hom).mp
  rw [changedArithmeticZeroAtlasIso_original_base]
  dsimp only [changedArithmeticAtlasIso, changedArithmeticAtlasToTwisted,
    changedArithmeticAtlasObject, twistedArithmeticAtlasObject, twistedArithmeticAtlasIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.refl_inv, Category.comp_id,
    Category.assoc, twistedRetainedOrientation_base,
    arithmeticRetainedFixedSmoothingIso_base]
  rw [arithmeticLabeledAtlasMap]
  exact arithmeticLabeledRetainedChart_base hπ data H m 1 hj _ b

/-- The installed whole last node after four rounds keeps the original quotient base. -/
@[reassoc] theorem arithmeticFourthOuterZeroLast_base (b : Bool) :
    (N b).hom ≫ ω (.retained ⟨0, by omega⟩ b) ≫ q = chartStructure Q τ := by
  apply (cancel_epi (arithmeticFourthAccumulatedLastIso hπ data H m 0 hj u hu b).hom).mp
  rw [arithmeticFourthAccumulatedLastIso_base]
  rw [arithmeticFourthAccumulatedLast_chart_assoc]
  exact changedArithmeticZeroAtlas_retained_base hπ data H m hj u hu b

local notation "t" => arithmeticFourthTerminalSmoothing hπ data H 0 hj u hu m
local notation "F" => arithmeticFourthOuterAtlasIso hπ data H m 0 hj u hu

/-- The complete original terminal comparison preserves its full scalar projection. -/
@[reassoc] theorem arithmeticFourthOuterZeroTerminalIso_base :
    (F .terminal).hom ≫ chartStructure Q t =
      arithmeticLabeledAtlasMap hπ data H m 1 hj .terminal ≫ S := by
  simp only [arithmeticFourthOuterAtlasIso, arithmeticFourthOuterAtlasCorrection,
    arithmeticFourthInitialAtlasCorrection, arithmeticFourthAtlasCorrection,
    arithmeticThirdInitialAtlasIso, arithmeticThirdInitialAtlasCorrection,
    arithmeticThirdAtlasIso, arithmeticThirdAtlasCorrection,
    arithmeticSecondJointAtlasIso, arithmeticSecondJointAtlasCorrection,
    arithmeticResidualLiftAtlasIso, arithmeticResidualLiftAtlasCorrection,
    changedArithmeticAtlasIso, changedArithmeticAtlasToTwisted,
    Iso.trans_hom, Iso.symm_symm_eq, Iso.refl_hom, Category.comp_id, Category.assoc]
  rw [arithmeticFourthTerminalIso_base, arithmeticThirdTerminalIso_base,
    arithmeticSecondResidualLiftTerminalIso_base, arithmeticResidualLiftTerminalIso_base,
    arithmeticTerminalChangedIso_base]
  dsimp only [twistedArithmeticAtlasIso]
  rw [arithmeticLabeledAtlasMap, arithmeticLabeledTerminalChart_base]
  exact WeierstrassDilatation.fixedTerminalPolygonIso_structure ..

/-- The actual fourth common terminal inclusion retains the full original global base. -/
@[reassoc] theorem arithmeticFourthOuterZeroTerminal_base :
    ω .terminal ≫ q = chartStructure Q t := by
  apply (cancel_epi (F .terminal).hom).mp
  rw [arithmeticFourthOuterZeroTerminalIso_base]
  rw [← Category.assoc, ← arithmeticFourthOuterAtlasIso_chart,
    arithmeticZeroDiagonalSourceToBase, Category.assoc, Iso.hom_inv_id_assoc]

end FLT.Mazur.WeierstrassDividedDepth
