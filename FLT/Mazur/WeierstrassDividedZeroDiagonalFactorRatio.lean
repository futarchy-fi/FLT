/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroInitialNodeTransport
public import FLT.Mazur.WeierstrassDividedZeroDiagonalPolygon
public import FLT.Mazur.WeierstrassDividedRevisedInitialMaps

/-!
# Full factor-ratio maps from the corrected diagonal initial opens

Transport the original polynomial factor ratio through the whole accumulated
node isomorphism. The domain is the actual finite pullback open; the two target
nodes retain their separate smoothings. Compatibility with other labels is separate.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFiniteInitialIso arithmeticInitialFactorRatioChart
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "N" => arithmeticInitialFactorRatioChart π m W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "E" => arithmeticZeroFiniteAtlasIso hπ data H m m hj u hu
local notation "D" => arithmeticZeroDiagonalState hπ data H 0 hj u hu
local notation "s" => PolygonArithmeticSimultaneous.State.initial D m

/-- The full finite node comparison identifies its parameter with the diagonal smoothing. -/
def arithmeticZeroDiagonalInitialTotalNodeIso (b : Bool) :
    PolygonSmoothing.chart Q τ ≅ PolygonSmoothing.chart Q (s b) :=
  arithmeticZeroFiniteInitialTotalNodeIso hπ data H m hj u hu m b ≪≫
    nodeParameterIso _ _ (arithmeticZeroDiagonalState_initial hπ data H 0 hj u hu m b).symm

local notation "T" => arithmeticZeroDiagonalInitialTotalNodeIso hπ data H m hj u hu

/-- The original full factor ratio is carried to the actual corrected initial open and node. -/
def arithmeticZeroDiagonalInitialFactorRatio (b : Bool) :
    arithmeticZeroFiniteInitialObject hπ data H m m 0 hj u hu b ⟶
      PolygonSmoothing.chart Q (s b) :=
  (E (.initial b)).inv ≫ N ≫ (T b).hom

local notation "F" => arithmeticZeroDiagonalInitialFactorRatio hπ data H m hj u hu

instance arithmeticZeroDiagonalInitialFactorRatio_isOpenImmersion (b : Bool) :
    IsOpenImmersion (F b) := by
  unfold arithmeticZeroDiagonalInitialFactorRatio
  infer_instance

/-- The whole original initial open recovers its full factor-ratio map. -/
@[reassoc] theorem arithmeticZeroDiagonalInitialFactorRatio_transport (b : Bool) :
    (E (.initial b)).hom ≫ F b = N ≫ (T b).hom := by
  rw [arithmeticZeroDiagonalInitialFactorRatio, Iso.hom_inv_id_assoc]

/-- The entire corrected initial node has its original cyclic orientation. -/
def arithmeticZeroDiagonalPolygonInitialMap (b : Bool) :
    PolygonSmoothing.chart Q (s b) ⟶ arithmeticZeroDiagonalPolygon hπ data H m hj u hu :=
  (if b then (branchSwapIso Q (s b)).hom else 𝟙 _) ≫
    arithmeticZeroDiagonalPolygonInitialChart hπ data H m hj u hu b

local notation "C" => arithmeticZeroDiagonalPolygonInitialMap hπ data H m hj u hu

instance arithmeticZeroDiagonalPolygonInitialMap_isOpenImmersion (b : Bool) :
    IsOpenImmersion (C b) := by
  unfold arithmeticZeroDiagonalPolygonInitialMap
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, Category.id_comp] <;> infer_instance

/-- Each full corrected source initial open maps to its independently constructed target node. -/
def arithmeticZeroDiagonalFactorRatioInitialMap (b : Bool) :
    arithmeticZeroFiniteInitialObject hπ data H m m 0 hj u hu b ⟶
      arithmeticZeroDiagonalPolygon hπ data H m hj u hu :=
  F b ≫ C b

local notation "f" => arithmeticZeroDiagonalFactorRatioInitialMap hπ data H m hj u hu

instance arithmeticZeroDiagonalFactorRatioInitialMap_isOpenImmersion (b : Bool) :
    IsOpenImmersion (f b) := by
  unfold arithmeticZeroDiagonalFactorRatioInitialMap
  infer_instance

/-- Transport preserves the complete original polynomial factor ratio at its actual label. -/
@[reassoc] theorem arithmeticZeroDiagonalFactorRatioInitialMap_transport (b : Bool) :
    (E (.initial b)).hom ≫ f b = N ≫ (T b).hom ≫ C b := by
  rw [arithmeticZeroDiagonalFactorRatioInitialMap, ← Category.assoc,
    arithmeticZeroDiagonalInitialFactorRatio_transport, Category.assoc]

/-- The full transported initial map reflects equality, including nilpotent arithmetic orders. -/
theorem arithmeticZeroDiagonalFactorRatioInitialMap_injective (b : Bool) :
    Function.Injective (f b) := (f b).isOpenEmbedding.injective

end FLT.Mazur.WeierstrassDividedDepth
