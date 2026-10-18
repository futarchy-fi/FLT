/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOneFiniteAtlas
public import FLT.Mazur.WeierstrassDividedOneFiniteState

/-!
# The complete diagonal depth-one atlas

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
  arithmeticFifthInitialAtlasChart arithmeticOneFiniteInitialIso arithmeticOneFiniteRetainedIso
  arithmeticOneFiniteTerminalIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 2 ≤ n)
  (u : Rˣ) (hu : (data ⟨2, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
/-- The actual diagonal chart objects, including the pulled-back initial open and infinity. -/
def arithmeticOneDiagonalAtlasObject : ArithmeticChartLabel 2 → Scheme :=
  arithmeticOneFiniteAtlasObject hπ data H m m hj u hu

local notation "A" => arithmeticOneDiagonalAtlasObject hπ data H m hj u hu
local notation "B" => arithmeticFifthInitialAtlasObject hπ data H m hj u hu

/-- The full correction from the original fifth chart at this arithmetic order. -/
def arithmeticOneDiagonalAtlasCorrection (i : ArithmeticChartLabel 2) : B i ≅ A i :=
  arithmeticOneFiniteAtlasCorrection hπ data H m m hj u hu i

/-- The diagonal charts are installed in the same complete original global target. -/
def arithmeticOneDiagonalAtlasChart (i : ArithmeticChartLabel 2) :
    A i ⟶ simultaneousTwistedArithmeticStage hπ data H m 1 hj u hu :=
  arithmeticOneFiniteAtlasChart hπ data H m m hj u hu i

local notation "E" => arithmeticOneDiagonalAtlasCorrection hπ data H m hj u hu
local notation "ι" => arithmeticOneDiagonalAtlasChart hπ data H m hj u hu

instance arithmeticOneDiagonalAtlasChart_isOpenImmersion (i : ArithmeticChartLabel 2) :
    IsOpenImmersion (ι i) := by
  unfold arithmeticOneDiagonalAtlasChart
  infer_instance

/-- Each complete diagonal correction recovers the exact fifth global inclusion. -/
@[reassoc] theorem arithmeticOneDiagonalAtlasCorrection_chart (i : ArithmeticChartLabel 2) :
    (E i).hom ≫ ι i = arithmeticFifthInitialAtlasChart hπ data H m hj u hu i :=
  arithmeticOneFiniteAtlasCorrection_chart hπ data H m m hj u hu i

/-- All labels of the complete target are covered at every diagonal order. -/
def arithmeticOneDiagonalOpenCover :
    (simultaneousTwistedArithmeticStage hπ data H m 1 hj u hu).OpenCover :=
  arithmeticOneFiniteOpenCover hπ data H m m hj u hu

/-- The diagonal atlas covers every point, including the original infinity chart. -/
theorem arithmeticOneDiagonalAtlas_cover
    (z : simultaneousTwistedArithmeticStage hπ data H m 1 hj u hu) :
    ∃ i x, ι i x = z := arithmeticOneFiniteAtlas_cover hπ data H m m hj u hu z

end FLT.Mazur.WeierstrassDividedDepth
