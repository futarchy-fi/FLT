/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroCyclicDiagonal
public import FLT.Mazur.WeierstrassDividedZeroCyclicIndex
public import FLT.Mazur.PolygonArithmeticCyclicNilpotence
public import FLT.Mazur.PolygonVariableSmoothingRestriction

/-!
# The independent standard variable-smoothing five-gon

Glue standard reciprocal Laurent edges with the five constructed diagonal
smoothings. Its full node charts and quotients are independent of the source atlas.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "D" => arithmeticZeroCyclicDiagonal hπ data H hj u hu
local notation "hD" => arithmeticZeroCyclicDiagonal_compatible hπ data H hj u hu
local notation "ha" => arithmeticZeroCyclicDiagonal_annihilated hπ data H hj u hu
local notation "Q" => fun m ↦ Quotient R π m

/-- The five independent target smoothings, in the standard predecessor order. -/
def arithmeticZeroCyclicStandardParameter (m : ℕ) (i : Fin 5) : Q m :=
  (D).parameter m (zeroCyclicIndex i)

local notation "t" => arithmeticZeroCyclicStandardParameter hπ data H hj u hu

instance arithmeticZeroCyclicStandardParameter_nilpotent (m : ℕ) (i : Fin 5) :
    Fact (IsNilpotent (t m i)) :=
  ⟨(D).parameter_isNilpotent hD ha m (zeroCyclicIndex i)⟩

/-- The independently glued full standard five-gon, with all five smoothing drifts. -/
def arithmeticZeroCyclicStandard (m : ℕ) : Scheme :=
  PolygonVariableSmoothing.scheme (Q m) 5 (t m) (by decide)

/-- Every complete standard node embeds in this independent target. -/
def arithmeticZeroCyclicStandardChart (m : ℕ) (i : Fin 5) :
    PolygonSmoothing.chart (Q m) (t m i) ⟶ arithmeticZeroCyclicStandard hπ data H hj u hu m :=
  PolygonVariableSmoothing.chart (Q m) 5 (t m) (by decide) i

local notation "c" => arithmeticZeroCyclicStandardChart hπ data H hj u hu

instance arithmeticZeroCyclicStandardChart_isOpenImmersion (m : ℕ) (i : Fin 5) :
    IsOpenImmersion (c m i) := by
  unfold arithmeticZeroCyclicStandardChart
  infer_instance

/-- The target identifies the full left and reciprocal right punctures on every edge. -/
@[reassoc] theorem arithmeticZeroCyclicStandard_overlap (m : ℕ) (i : Fin 5) :
    leftBranchOpen (Q m) (t m i) ≫ c m i =
      precedingBranch (Q m) (t m ((finRotate 5).symm i)) ≫ c m ((finRotate 5).symm i) :=
  PolygonVariableSmoothing.overlap (Q m) 5 (t m) (by decide) i

/-- These five entire node charts cover the whole independently constructed target. -/
theorem arithmeticZeroCyclicStandard_cover (m : ℕ)
    (x : arithmeticZeroCyclicStandard hπ data H hj u hu m) : ∃ i y, c m i y = x :=
  PolygonVariableSmoothing.charts_cover (Q m) 5 (t m) (by decide) x

/-- The whole target retains the actual original coefficient restriction at each node. -/
def arithmeticZeroCyclicStandardRestriction (m : ℕ) :
    arithmeticZeroCyclicStandard hπ data H hj u hu m ⟶
      arithmeticZeroCyclicStandard hπ data H hj u hu (m + 1) :=
  PolygonVariableSmoothing.parameterProjection (restriction R π m).toRingHom 5
    (t (m + 1)) (t m) (fun i ↦ (hD).1 m (zeroCyclicIndex i)) (by decide)

/-- Each entire standard chart has its full coefficient square. -/
@[reassoc] theorem arithmeticZeroCyclicStandardChart_restriction (m : ℕ) (i : Fin 5) :
    c m i ≫ arithmeticZeroCyclicStandardRestriction hπ data H hj u hu m =
      Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom
        (t (m + 1) i) (t m i) ((hD).1 m (zeroCyclicIndex i)))) ≫ c (m + 1) i :=
  PolygonVariableSmoothing.chart_parameterProjection (restriction R π m).toRingHom 5
    (t (m + 1)) (t m) (fun i ↦ (hD).1 m (zeroCyclicIndex i)) (by decide) i

end FLT.Mazur.WeierstrassDividedDepth
