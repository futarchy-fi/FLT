/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroFiniteAtlas
public import FLT.Mazur.WeierstrassDividedZeroDiagonalState

/-!
# The complete diagonal depth-zero atlas

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
  arithmeticZeroFifthAtlasChart arithmeticZeroFiniteInitialIso arithmeticZeroFiniteLastIso
  arithmeticZeroFiniteTerminalIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
/-- The actual diagonal chart objects, including the pulled-back initial open and infinity. -/
def arithmeticZeroDiagonalAtlasObject : ArithmeticChartLabel 1 → Scheme :=
  arithmeticZeroFiniteAtlasObject hπ data H m m hj u hu

local notation "A" => arithmeticZeroDiagonalAtlasObject hπ data H m hj u hu
local notation "B" => arithmeticZeroFifthAtlasObject hπ data H m hj u hu

/-- The full correction from the original fifth chart at this arithmetic order. -/
def arithmeticZeroDiagonalAtlasCorrection (i : ArithmeticChartLabel 1) : B i ≅ A i :=
  arithmeticZeroFiniteAtlasCorrection hπ data H m m hj u hu i

/-- The diagonal charts are installed in the same complete original global target. -/
def arithmeticZeroDiagonalAtlasChart (i : ArithmeticChartLabel 1) :
    A i ⟶ simultaneousTwistedArithmeticStage hπ data H m 0 hj u hu :=
  arithmeticZeroFiniteAtlasChart hπ data H m m hj u hu i

local notation "E" => arithmeticZeroDiagonalAtlasCorrection hπ data H m hj u hu
local notation "ι" => arithmeticZeroDiagonalAtlasChart hπ data H m hj u hu

instance arithmeticZeroDiagonalAtlasChart_isOpenImmersion (i : ArithmeticChartLabel 1) :
    IsOpenImmersion (ι i) := by
  unfold arithmeticZeroDiagonalAtlasChart
  infer_instance

/-- Each complete diagonal correction recovers the exact fifth global inclusion. -/
@[reassoc] theorem arithmeticZeroDiagonalAtlasCorrection_chart (i : ArithmeticChartLabel 1) :
    (E i).hom ≫ ι i = arithmeticZeroFifthAtlasChart hπ data H m hj u hu i :=
  arithmeticZeroFiniteAtlasCorrection_chart hπ data H m m hj u hu i

/-- All labels of the complete target are covered at every diagonal order. -/
def arithmeticZeroDiagonalOpenCover :
    (simultaneousTwistedArithmeticStage hπ data H m 0 hj u hu).OpenCover :=
  arithmeticZeroFiniteOpenCover hπ data H m m hj u hu

/-- The diagonal atlas covers every point, including the original infinity chart. -/
theorem arithmeticZeroDiagonalAtlas_cover
    (z : simultaneousTwistedArithmeticStage hπ data H m 0 hj u hu) :
    ∃ i x, ι i x = z := arithmeticZeroFiniteAtlas_cover hπ data H m m hj u hu z

end FLT.Mazur.WeierstrassDividedDepth
