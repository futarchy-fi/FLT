/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroDiagonalPolygonParameters
public import FLT.Mazur.PolygonVariableSmoothingIdentifiedBase

/-!
# An independent polygon with the actual depth-zero diagonal smoothings

Every full target node uses its accumulated parameter, including the two
initial nodes and the common terminal. No global source comparison is assumed.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "p" => arithmeticZeroDiagonalPolygonParameter hπ data H hj u hu m
local notation "D" => arithmeticZeroDiagonalState hπ data H 0 hj u hu

/-- The independent cyclic target uses all five actual diagonal node parameters. -/
def arithmeticZeroDiagonalPolygon : Scheme :=
  PolygonVariableSmoothing.scheme Q 5 p (by omega)

/-- Each complete variable-smoothing node is embedded at its actual cyclic label. -/
def arithmeticZeroDiagonalPolygonChart (i : Fin 5) :
    PolygonSmoothing.chart Q (p i) ⟶ arithmeticZeroDiagonalPolygon hπ data H m hj u hu :=
  PolygonVariableSmoothing.chart Q 5 p (by omega) i

/-- The complete common terminal is included with its accumulated inverse drift. -/
def arithmeticZeroDiagonalPolygonTerminalChart :
    PolygonSmoothing.chart Q ((D).terminal m) ⟶
      arithmeticZeroDiagonalPolygon hπ data H m hj u hu :=
  PolygonVariableSmoothing.chartWithParameter Q 5 p (by omega) 0 ((D).terminal m) rfl

/-- Both full initial target nodes retain their separate diagonal smoothings. -/
def arithmeticZeroDiagonalPolygonInitialChart (b : Bool) :
    PolygonSmoothing.chart Q ((D).initial m b) ⟶
      arithmeticZeroDiagonalPolygon hπ data H m hj u hu :=
  PolygonVariableSmoothing.chartWithParameter Q 5 p (by omega) (initialPolygonIndex 1 b)
    ((D).initial m b) (arithmeticZeroDiagonalPolygonParameter_initial hπ data H hj u hu m b).symm

/-- Both retained target nodes keep the actual final smoothing on their own arm. -/
def arithmeticZeroDiagonalPolygonRetainedChart (b : Bool) :
    PolygonSmoothing.chart Q ((D).last m b) ⟶
      arithmeticZeroDiagonalPolygon hπ data H m hj u hu :=
  PolygonVariableSmoothing.chartWithParameter Q 5 p (by omega) (retainedPolygonIndex 1 0 b)
    ((D).last m b)
    (arithmeticZeroDiagonalPolygonParameter_retained hπ data H hj u hu m 0 b).symm

instance arithmeticZeroDiagonalPolygonChart_isOpenImmersion (i : Fin 5) :
    IsOpenImmersion (arithmeticZeroDiagonalPolygonChart hπ data H m hj u hu i) := by
  unfold arithmeticZeroDiagonalPolygonChart
  infer_instance

instance arithmeticZeroDiagonalPolygonInitialChart_isOpenImmersion (b : Bool) :
    IsOpenImmersion (arithmeticZeroDiagonalPolygonInitialChart hπ data H m hj u hu b) := by
  unfold arithmeticZeroDiagonalPolygonInitialChart
  infer_instance

instance arithmeticZeroDiagonalPolygonRetainedChart_isOpenImmersion (b : Bool) :
    IsOpenImmersion (arithmeticZeroDiagonalPolygonRetainedChart hπ data H m hj u hu b) := by
  unfold arithmeticZeroDiagonalPolygonRetainedChart
  infer_instance

/-- The independent target retains a full node cover. -/
def arithmeticZeroDiagonalPolygonOpenCover :
    (arithmeticZeroDiagonalPolygon hπ data H m hj u hu).OpenCover :=
  PolygonVariableSmoothing.chartCover Q 5 p (by omega)

/-- The coefficient projection glues the original quotient structure on every node. -/
def arithmeticZeroDiagonalPolygonToBase :
    arithmeticZeroDiagonalPolygon hπ data H m hj u hu ⟶ Spec (.of Q) :=
  PolygonVariableSmoothing.toBase Q 5 p (by omega)

local notation "B" => arithmeticZeroDiagonalPolygonToBase hπ data H m hj u hu

/-- Every full target node has its actual quotient coefficient projection. -/
@[reassoc] theorem arithmeticZeroDiagonalPolygonChart_base (i : Fin 5) :
    arithmeticZeroDiagonalPolygonChart hπ data H m hj u hu i ≫ B = chartStructure Q (p i) :=
  PolygonVariableSmoothing.chart_toBase Q 5 p (by omega) i

/-- Both initial target projections keep their separate accumulated smoothings. -/
@[reassoc] theorem arithmeticZeroDiagonalPolygonInitialChart_base (b : Bool) :
    arithmeticZeroDiagonalPolygonInitialChart hπ data H m hj u hu b ≫ B =
      chartStructure Q ((D).initial m b) :=
  PolygonVariableSmoothing.chartWithParameter_toBase Q 5 p (by omega) _ _ _

/-- Both retained target projections keep their actual diagonal last-node parameters. -/
@[reassoc] theorem arithmeticZeroDiagonalPolygonRetainedChart_base (b : Bool) :
    arithmeticZeroDiagonalPolygonRetainedChart hπ data H m hj u hu b ≫ B =
      chartStructure Q ((D).last m b) :=
  PolygonVariableSmoothing.chartWithParameter_toBase Q 5 p (by omega) _ _ _

/-- Every adjacent target quotient uses the actual separate diagonal coefficient maps. -/
def arithmeticZeroDiagonalPolygonRestriction :
    arithmeticZeroDiagonalPolygon hπ data H m hj u hu ⟶
      arithmeticZeroDiagonalPolygon hπ data H (m + 1) hj u hu :=
  PolygonVariableSmoothing.parameterProjection (restriction R π m).toRingHom 5
    (arithmeticZeroDiagonalPolygonParameter hπ data H hj u hu (m + 1)) p
    (arithmeticZeroDiagonalPolygonParameter_restriction hπ data H hj u hu m) (by omega)

/-- Every full target chart retains its actual diagonal quotient square. -/
@[reassoc] theorem arithmeticZeroDiagonalPolygonChart_restriction (i : Fin 5) :
    arithmeticZeroDiagonalPolygonChart hπ data H m hj u hu i ≫
      arithmeticZeroDiagonalPolygonRestriction hπ data H m hj u hu =
        Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom
          (arithmeticZeroDiagonalPolygonParameter hπ data H hj u hu (m + 1) i) (p i)
          (arithmeticZeroDiagonalPolygonParameter_restriction hπ data H hj u hu m i))) ≫
            arithmeticZeroDiagonalPolygonChart hπ data H (m + 1) hj u hu i :=
  PolygonVariableSmoothing.chart_parameterProjection _ 5 _ p _ (by omega) i

/-- The complete new target restriction lies over the original quotient homomorphism. -/
@[reassoc] theorem arithmeticZeroDiagonalPolygonRestriction_base :
    arithmeticZeroDiagonalPolygonRestriction hπ data H m hj u hu ≫
      arithmeticZeroDiagonalPolygonToBase hπ data H (m + 1) hj u hu =
        B ≫ Spec.map (CommRingCat.ofHom (restriction R π m).toRingHom) :=
  PolygonVariableSmoothing.parameterProjection_base _ 5 _ p _ (by omega)

end FLT.Mazur.WeierstrassDividedDepth
