/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOneInfinityNormalizedPairBase
public import FLT.Mazur.WeierstrassDividedOneRetainedNodeBase
public import FLT.Mazur.WeierstrassDividedOriginalNodeBase
public import FLT.Mazur.WeierstrassDividedFifthInitialAtlasIdentification

/-!
# The entire first retained nodes retain the actual original global base

The composed full atlas isomorphism includes every predecessor correction.
Its scalar square identifies the original global base on the entire node.
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
  arithmeticOneFiniteRetainedIso arithmeticSecondPrecedingOrientedIso
  arithmeticThirdPrecedingIso arithmeticFourthInitialNeighborIso arithmeticFifthInitialNeighborIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 2 ≤ n)
  (u : Rˣ) (hu : (data ⟨2, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "E" => arithmeticOneFiniteAtlasIso hπ data H m m hj u hu
local notation "c" => arithmeticOneDiagonalAtlasChart hπ data H m hj u hu
local notation "q" => arithmeticOneDiagonalSourceToBase hπ data H m hj u hu
local notation "D" => arithmeticOneDiagonalState hπ data H hj u hu

local notation "a" => fun b ↦ ArithmeticChartLabel.retained (⟨0, by omega⟩ : Fin 2) b
local notation "C₀" => changedArithmeticAtlasChart hπ data H m 1 hj u hu
local notation "E₀" => changedArithmeticAtlasIso hπ data H m 1 hj u hu
local notation "C₁" => arithmeticResidualLiftAtlasChart hπ data H m 1 hj u hu
local notation "C₂" => arithmeticSecondJointAtlasChart hπ data H m 1 hj u hu
local notation "M₂" => arithmeticSecondJointPrecedingIdentification hπ data H m 1 hj u hu 0 rfl
local notation "C₃" => arithmeticThirdAtlasChart hπ data H m 1 hj u hu
local notation "M₃" => arithmeticThirdPrecedingIdentification hπ data H m 1 hj u hu 0 rfl
local notation "C₄" => arithmeticFourthInitialAtlasChart hπ data H m 1 hj u hu
local notation "M₄" => arithmeticFourthInitialNeighborIdentification hπ data H m 1 hj u hu rfl
local notation "C₅" => arithmeticFifthInitialAtlasChart hπ data H m hj u hu

/-- The original oriented retained-0 chart keeps its actual global base. -/
@[reassoc] theorem arithmeticOneChangedRetainedFirst_base (b : Bool) :
    C₀ (.retained (0 : Fin 2) b) ≫ q = chartStructure Q τ := by
  apply (cancel_epi (E₀ (.retained (0 : Fin 2) b)).hom).mp
  rw [← Category.assoc, ← changedArithmeticAtlasIso_chart,
    arithmeticOneDiagonalSourceToBase, Category.assoc, Iso.hom_inv_id_assoc]
  dsimp only [changedArithmeticAtlasIso, changedArithmeticAtlasToTwisted,
    changedArithmeticAtlasObject, twistedArithmeticAtlasObject, twistedArithmeticAtlasIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.refl_inv, Category.comp_id,
    Category.assoc, twistedRetainedOrientation_base, arithmeticRetainedFixedSmoothingIso_base]
  rw [arithmeticLabeledAtlasMap]
  exact arithmeticLabeledRetainedChart_base hπ data H m 2 hj _ b

/-- The unchanged first retained label after the first closing correction keeps its base. -/
@[reassoc] theorem arithmeticOneResidualRetainedFirst_base (b : Bool) :
    C₁ (.retained (0 : Fin 2) b) ≫ q = chartStructure Q τ := by
  simpa only [arithmeticResidualLiftAtlasObject, arithmeticResidualLiftAtlasChart,
    arithmeticResidualLiftAtlasCorrection,
    Fin.val_zero, Nat.zero_ne_one, ↓reduceIte, Iso.refl_inv, Category.id_comp] using
    arithmeticOneChangedRetainedFirst_base hπ data H m hj u hu b

/-- The full second predecessor chart has its original global coefficient map. -/
@[reassoc] theorem arithmeticOneSecondRetainedFirst_base (b : Bool) :
    (M₂ b).hom ≫ C₂ (.retained (0 : Fin 2) b) ≫ q =
      chartStructure Q (arithmeticSecondPrecedingSmoothing hπ data H m 1 hj u hu b) := by
  apply (cancel_epi (arithmeticSecondPrecedingOrientedIso hπ data H m 1 hj u hu b).hom).mp
  erw [arithmeticSecondJointPreceding_chart_assoc, arithmeticOneResidualRetainedFirst_base,
    arithmeticOneSecondPrecedingOrientedIso_base]

/-- The full third predecessor chart has its original global coefficient map. -/
@[reassoc] theorem arithmeticOneThirdRetainedFirst_base (b : Bool) :
    (M₃ b).hom ≫ C₃ (.retained (0 : Fin 2) b) ≫ q =
      chartStructure Q (arithmeticThirdPrecedingSmoothing hπ data H 1 hj u hu m b) := by
  apply (cancel_epi (arithmeticThirdPrecedingIso hπ data H m 1 hj u hu b).hom).mp
  erw [arithmeticThirdPreceding_chart_assoc, arithmeticOneSecondRetainedFirst_base,
    arithmeticOneThirdPrecedingIso_base]

/-- Installing the original initial open does not change the predecessor's full base. -/
@[reassoc] theorem arithmeticOneThirdInitialRetainedFirst_base (b : Bool) :
    (M₃ b).hom ≫
      arithmeticThirdInitialAtlasChart hπ data H m 1 hj u hu (.retained (0 : Fin 2) b) ≫ q =
      chartStructure Q (arithmeticThirdPrecedingSmoothing hπ data H 1 hj u hu m b) := by
  simpa only [arithmeticThirdInitialAtlasObject, arithmeticThirdInitialAtlasChart,
    arithmeticThirdInitialAtlasCorrection,
    Iso.refl_inv, Category.id_comp] using
    arithmeticOneThirdRetainedFirst_base hπ data H m hj u hu b

/-- The fourth full predecessor chart has its original global coefficient map. -/
@[reassoc] theorem arithmeticOneFourthRetainedFirst_base (b : Bool) :
    (M₄ b).hom ≫ C₄ (.retained (0 : Fin 2) b) ≫ q =
      chartStructure Q (arithmeticFourthInitialNeighborSmoothing hπ data H 1 hj u hu m b) := by
  apply (cancel_epi (arithmeticFourthInitialNeighborIso hπ data H m 1 hj u hu b).hom).mp
  erw [arithmeticFourthInitialNeighbor_chart_assoc, arithmeticOneThirdInitialRetainedFirst_base,
    arithmeticOneFourthNeighborIso_base]

/-- The whole fifth retained-0 node has its original global coefficient projection. -/
@[reassoc] theorem arithmeticOneFifthRetainedFirst_base (b : Bool) :
    C₅ (.retained (0 : Fin 2) b) ≫ q =
      chartStructure Q (arithmeticFifthInitialNeighborSmoothing hπ data H 1 hj u hu m b) := by
  apply (cancel_epi (arithmeticFifthInitialNeighborIso hπ data H m 1 hj u hu b).hom).mp
  erw [arithmeticFifthInitialNeighbor_chart_assoc, arithmeticOneFourthRetainedFirst_base,
    arithmeticOneFifthNeighborIso_base]

/-- Both entire retained-0 source charts carry the original global coefficient projection. -/
@[reassoc] theorem arithmeticOneDiagonalAtlas_retainedFirst_base (b : Bool) :
    c (.retained (0 : Fin 2) b) ≫ q = chartStructure Q ((D).retained m 0 b) := by
  let P := arithmeticOneFiniteRetainedIso hπ data H m m hj u hu 0 b
  have hP : P.hom ≫ c (.retained (0 : Fin 2) b) = C₅ (.retained (0 : Fin 2) b) := by
    simpa only [arithmeticOneFiniteAtlasCorrection, arithmeticOneDiagonalAtlasChart] using
      arithmeticOneFiniteAtlasCorrection_chart hπ data H m m hj u hu (.retained (0 : Fin 2) b)
  apply (cancel_epi P.hom).mp
  rw [← Category.assoc, hP, arithmeticOneFifthRetainedFirst_base]
  exact (arithmeticOneFiniteRetainedIso_base hπ data H m hj u hu m 0 b).symm

end FLT.Mazur.WeierstrassDividedDepth
