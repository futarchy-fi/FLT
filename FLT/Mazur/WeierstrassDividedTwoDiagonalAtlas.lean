/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTwoFiniteAtlas
public import FLT.Mazur.WeierstrassDividedTwoFiniteAtlasClosing
public import FLT.Mazur.WeierstrassDividedTwoFiniteAtlasIncoming
public import FLT.Mazur.WeierstrassDividedTwoFiniteAtlasInitial
public import FLT.Mazur.WeierstrassDividedTwoFiniteState

/-!
# The complete diagonal depth-two atlas

Use m further measured corrections at arithmetic order m. Every chart retains
its actual finite smoothing and the initial pullback open; infinity and the
complete original global target are unchanged.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFifthShallowAtlasChart arithmeticTwoFiniteInitialIso arithmeticTwoFiniteRetainedIso
  arithmeticTwoFiniteTerminalIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 3 ≤ n)
  (u : Rˣ) (hu : (data ⟨3, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
/-- The actual diagonal chart objects, including the pulled-back initial open and infinity. -/
def arithmeticTwoDiagonalAtlasObject : ArithmeticChartLabel 3 → Scheme :=
  arithmeticTwoFiniteAtlasObject hπ data H m m hj u hu

local notation "A" => arithmeticTwoDiagonalAtlasObject hπ data H m hj u hu
local notation "B" => arithmeticFifthShallowAtlasObject hπ data H m hj u hu

/-- The full correction from the original fifth chart at this arithmetic order. -/
def arithmeticTwoDiagonalAtlasCorrection (i : ArithmeticChartLabel 3) : B i ≅ A i :=
  arithmeticTwoFiniteAtlasCorrection hπ data H m m hj u hu i

/-- The diagonal charts are installed in the same complete original global target. -/
def arithmeticTwoDiagonalAtlasChart (i : ArithmeticChartLabel 3) :
    A i ⟶ simultaneousTwistedArithmeticStage hπ data H m 2 hj u hu :=
  arithmeticTwoFiniteAtlasChart hπ data H m m hj u hu i

local notation "E" => arithmeticTwoDiagonalAtlasCorrection hπ data H m hj u hu
local notation "ι" => arithmeticTwoDiagonalAtlasChart hπ data H m hj u hu

instance arithmeticTwoDiagonalAtlasChart_isOpenImmersion (i : ArithmeticChartLabel 3) :
    IsOpenImmersion (ι i) := by
  unfold arithmeticTwoDiagonalAtlasChart
  infer_instance

/-- Each complete diagonal correction recovers the exact fifth global inclusion. -/
@[reassoc] theorem arithmeticTwoDiagonalAtlasCorrection_chart (i : ArithmeticChartLabel 3) :
    (E i).hom ≫ ι i = arithmeticFifthShallowAtlasChart hπ data H m hj u hu i :=
  arithmeticTwoFiniteAtlasCorrection_chart hπ data H m m hj u hu i

/-- All labels of the complete target are covered at every diagonal order. -/
def arithmeticTwoDiagonalOpenCover :
    (simultaneousTwistedArithmeticStage hπ data H m 2 hj u hu).OpenCover :=
  arithmeticTwoFiniteOpenCover hπ data H m m hj u hu

/-- The diagonal atlas covers every point, including the original infinity chart. -/
theorem arithmeticTwoDiagonalAtlas_cover
    (z : simultaneousTwistedArithmeticStage hπ data H m 2 hj u hu) :
    ∃ i x, ι i x = z := arithmeticTwoFiniteAtlas_cover hπ data H m m hj u hu z

end FLT.Mazur.WeierstrassDividedDepth

/-!
# Normalized overlaps in the complete diagonal atlas

At each arithmetic order, the initial edge retains its complete original
Mobius/right base and both closing branches have identity transition.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFifthShallowAtlasChart arithmeticTwoFiniteInitialIso arithmeticTwoFiniteRetainedIso
  arithmeticTwoFiniteTerminalIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 3 ≤ n)
  (u : Rˣ) (hu : (data ⟨3, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "ι" => arithmeticTwoDiagonalAtlasChart hπ data H m hj u hu
local notation "D" => arithmeticTwoDiagonalState hπ data H hj u hu

/-- The actual diagonal initial overlap equals its full original base at every order. -/
@[reassoc] theorem arithmeticTwoDiagonalAtlas_initial_normalized (b : Bool) :
    arithmeticTwoFiniteInitialPuncture hπ data H m m hj u hu b ≫ ι (.initial b) =
      (punctureSpecIso (arithmeticInitialBaseEquiv data H m 2 hj)).hom ≫
        rightBranchOpen Q ((D).retained m 0 b) ≫ ι (.retained ⟨0, by omega⟩ b) :=
  arithmeticTwoFiniteAtlas_initial_normalized hπ data H m m hj u hu (by omega) b

/-- Both actual diagonal closing overlaps are standard at every arithmetic order. -/
@[reassoc] theorem arithmeticTwoDiagonalAtlas_closing_normalized (b : Bool) :
    (edgeInversion Q).hom ≫ leftBranchOpen Q ((D).retained m 2 b) ≫
        ι (.retained (2 : Fin 3) b) =
      punctureOpen ((D).terminal m) b ≫ ι .terminal :=
  arithmeticTwoFiniteAtlas_closing_normalized hπ data H m m hj u hu (by omega) b

/-- Both internal diagonal overlaps are standard at every arithmetic order. -/
@[reassoc] theorem arithmeticTwoDiagonalAtlas_incoming_normalized (b : Bool) :
    (edgeInversion Q).hom ≫ leftBranchOpen Q ((D).retained m 1 b) ≫ ι (.retained 1 b) =
      rightBranchOpen Q ((D).retained m 2 b) ≫ ι (.retained 2 b) :=
  arithmeticTwoFiniteAtlas_incoming_normalized hπ data H m m hj u hu (by omega) b

/-- Both preceding diagonal overlaps are standard at every arithmetic order. -/
@[reassoc] theorem arithmeticTwoDiagonalAtlas_preceding_normalized (b : Bool) :
    (edgeInversion Q).hom ≫ leftBranchOpen Q ((D).retained m 0 b) ≫ ι (.retained 0 b) =
      rightBranchOpen Q ((D).retained m 1 b) ≫ ι (.retained 1 b) :=
  arithmeticTwoFiniteAtlas_preceding_normalized hπ data H m m hj u hu (by omega) b

end FLT.Mazur.WeierstrassDividedDepth
