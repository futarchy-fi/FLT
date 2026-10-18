/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedThreeFiniteAtlas
public import FLT.Mazur.WeierstrassDividedThreeFiniteAtlasClosing
public import FLT.Mazur.WeierstrassDividedThreeFiniteAtlasIncoming
public import FLT.Mazur.WeierstrassDividedThreeFiniteAtlasInitial
public import FLT.Mazur.WeierstrassDividedThreeFiniteState

/-!
# The complete diagonal depth-three atlas

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
  arithmeticThreeSeedAtlasChart arithmeticThreeFiniteInitialIso arithmeticThreeFiniteRetainedIso
  arithmeticThreeFiniteTerminalIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 4 ≤ n)
  (u : Rˣ) (hu : (data ⟨4, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
/-- The actual diagonal chart objects, including the pulled-back initial open and infinity. -/
def arithmeticThreeDiagonalAtlasObject : ArithmeticChartLabel 4 → Scheme :=
  arithmeticThreeFiniteAtlasObject hπ data H m m hj u hu

local notation "A" => arithmeticThreeDiagonalAtlasObject hπ data H m hj u hu
local notation "B" => arithmeticThreeSeedAtlasObject hπ data H m hj u hu

/-- The full correction from the original fifth chart at this arithmetic order. -/
def arithmeticThreeDiagonalAtlasCorrection (i : ArithmeticChartLabel 4) : B i ≅ A i :=
  arithmeticThreeFiniteAtlasCorrection hπ data H m m hj u hu i

/-- The diagonal charts are installed in the same complete original global target. -/
def arithmeticThreeDiagonalAtlasChart (i : ArithmeticChartLabel 4) :
    A i ⟶ simultaneousTwistedArithmeticStage hπ data H m 3 hj u hu :=
  arithmeticThreeFiniteAtlasChart hπ data H m m hj u hu i

local notation "E" => arithmeticThreeDiagonalAtlasCorrection hπ data H m hj u hu
local notation "ι" => arithmeticThreeDiagonalAtlasChart hπ data H m hj u hu

instance arithmeticThreeDiagonalAtlasChart_isOpenImmersion (i : ArithmeticChartLabel 4) :
    IsOpenImmersion (ι i) := by
  unfold arithmeticThreeDiagonalAtlasChart
  infer_instance

/-- Each complete diagonal correction recovers the exact fifth global inclusion. -/
@[reassoc] theorem arithmeticThreeDiagonalAtlasCorrection_chart (i : ArithmeticChartLabel 4) :
    (E i).hom ≫ ι i = arithmeticThreeSeedAtlasChart hπ data H m hj u hu i :=
  arithmeticThreeFiniteAtlasCorrection_chart hπ data H m m hj u hu i

/-- All labels of the complete target are covered at every diagonal order. -/
def arithmeticThreeDiagonalOpenCover :
    (simultaneousTwistedArithmeticStage hπ data H m 3 hj u hu).OpenCover :=
  arithmeticThreeFiniteOpenCover hπ data H m m hj u hu

/-- The diagonal atlas covers every point, including the original infinity chart. -/
theorem arithmeticThreeDiagonalAtlas_cover
    (z : simultaneousTwistedArithmeticStage hπ data H m 3 hj u hu) :
    ∃ i x, ι i x = z := arithmeticThreeFiniteAtlas_cover hπ data H m m hj u hu z

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
  arithmeticThreeSeedAtlasChart arithmeticThreeFiniteInitialIso arithmeticThreeFiniteRetainedIso
  arithmeticThreeFiniteTerminalIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 4 ≤ n)
  (u : Rˣ) (hu : (data ⟨4, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "ι" => arithmeticThreeDiagonalAtlasChart hπ data H m hj u hu
local notation "D" => arithmeticThreeDiagonalState hπ data H hj u hu

/-- The actual diagonal initial overlap equals its full original base at every order. -/
@[reassoc] theorem arithmeticThreeDiagonalAtlas_initial_normalized (b : Bool) :
    arithmeticThreeFiniteInitialPuncture hπ data H m m hj u hu b ≫ ι (.initial b) =
      (punctureSpecIso (arithmeticInitialBaseEquiv data H m 3 hj)).hom ≫
        rightBranchOpen Q ((D).retained m 0 b) ≫ ι (.retained ⟨0, by omega⟩ b) :=
  arithmeticThreeFiniteAtlas_initial_normalized hπ data H m m hj u hu (by omega) b

/-- Both actual diagonal closing overlaps are standard at every arithmetic order. -/
@[reassoc] theorem arithmeticThreeDiagonalAtlas_closing_normalized (b : Bool) :
    (edgeInversion Q).hom ≫ leftBranchOpen Q ((D).retained m 3 b) ≫
        ι (.retained (3 : Fin 4) b) =
      punctureOpen ((D).terminal m) b ≫ ι .terminal :=
  arithmeticThreeFiniteAtlas_closing_normalized hπ data H m m hj u hu (by omega) b

/-- All three internal diagonal overlaps are standard at every arithmetic order. -/
@[reassoc] theorem arithmeticThreeDiagonalAtlas_incoming_normalized (i : Fin 3) (b : Bool) :
    (edgeInversion Q).hom ≫ leftBranchOpen Q ((D).retained m i.castSucc b) ≫
        ι (.retained i.castSucc b) =
      rightBranchOpen Q ((D).retained m i.succ b) ≫ ι (.retained i.succ b) :=
  arithmeticThreeFiniteAtlas_incoming_normalized hπ data H m m hj u hu i (by omega) b

end FLT.Mazur.WeierstrassDividedDepth
