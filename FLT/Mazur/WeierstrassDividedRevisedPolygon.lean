/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRevisedPolygonParameters
public import FLT.Mazur.PolygonVariableSmoothingChartIdentification

/-!
# The revised arithmetic polygon as an independent cyclic target

This target is constructed directly from its cyclic diagram and node parameters,
not from the transported original open cover. Its full node inclusions retain
the original terminal, initial and retained labels.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R} {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "N" => 2 * (j + 1) + 3
local notation "p" => arithmeticRevisedPolygonParameter data H m j hj u hu
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "σ" => arithmeticTerminalChangedSmoothing data H m j hj u hu

/-- The full cyclic gluing with its actual terminal parameter and unchanged exterior nodes. -/
def arithmeticRevisedPolygon : Scheme :=
  PolygonVariableSmoothing.scheme Q N p (by omega)

/-- Every full node of the independently constructed cyclic target. -/
def arithmeticRevisedPolygonChart (i : Fin N) :
    PolygonSmoothing.chart Q (p i) ⟶ arithmeticRevisedPolygon data H m j hj u hu :=
  PolygonVariableSmoothing.chart Q N p (by omega) i

/-- The unchanged full retained chart at its original cyclic label. -/
def arithmeticRevisedPolygonRetainedChart (a : Fin (j + 1)) (b : Bool) :
    PolygonSmoothing.chart Q τ ⟶ arithmeticRevisedPolygon data H m j hj u hu :=
  PolygonVariableSmoothing.chartWithParameter Q N p (by omega)
    (retainedPolygonIndex (j + 1) a b) τ
    (arithmeticRevisedPolygonParameter_retained data H m j hj u hu a b).symm

/-- The common terminal chart uses the changed smoothing at label zero. -/
def arithmeticRevisedPolygonTerminalChart :
    PolygonSmoothing.chart Q σ ⟶ arithmeticRevisedPolygon data H m j hj u hu :=
  PolygonVariableSmoothing.chartWithParameter Q N p (by omega) 0 σ
    (arithmeticRevisedPolygonParameter_terminal data H m j hj u hu).symm

/-- Both full initial nodes remain available for the original initial open comparisons. -/
def arithmeticRevisedPolygonInitialChart (b : Bool) :
    PolygonSmoothing.chart Q τ ⟶ arithmeticRevisedPolygon data H m j hj u hu :=
  PolygonVariableSmoothing.chartWithParameter Q N p (by omega)
    (initialPolygonIndex (j + 1) b) τ
    (arithmeticRevisedPolygonParameter_initial data H m j hj u hu b).symm

instance arithmeticRevisedPolygonChart_isOpenImmersion (i : Fin N) :
    IsOpenImmersion (arithmeticRevisedPolygonChart data H m j hj u hu i) := by
  unfold arithmeticRevisedPolygonChart
  infer_instance

instance arithmeticRevisedPolygonRetainedChart_isOpenImmersion
    (a : Fin (j + 1)) (b : Bool) :
    IsOpenImmersion (arithmeticRevisedPolygonRetainedChart data H m j hj u hu a b) := by
  unfold arithmeticRevisedPolygonRetainedChart
  infer_instance

instance arithmeticRevisedPolygonTerminalChart_isOpenImmersion :
    IsOpenImmersion (arithmeticRevisedPolygonTerminalChart data H m j hj u hu) := by
  unfold arithmeticRevisedPolygonTerminalChart
  infer_instance

instance arithmeticRevisedPolygonInitialChart_isOpenImmersion (b : Bool) :
    IsOpenImmersion (arithmeticRevisedPolygonInitialChart data H m j hj u hu b) := by
  unfold arithmeticRevisedPolygonInitialChart
  infer_instance

/-- The independently glued target is covered by all its complete node charts. -/
def arithmeticRevisedPolygonOpenCover : (arithmeticRevisedPolygon data H m j hj u hu).OpenCover :=
  PolygonVariableSmoothing.chartCover Q N p (by omega)

/-- Its arithmetic base map retains every node's original coefficient ring. -/
def arithmeticRevisedPolygonToBase :
    arithmeticRevisedPolygon data H m j hj u hu ⟶ Spec (.of Q) :=
  PolygonVariableSmoothing.toBase Q N p (by omega)

instance arithmeticRevisedPolygonToBase_flat :
    Flat (arithmeticRevisedPolygonToBase data H m j hj u hu) := by
  unfold arithmeticRevisedPolygonToBase
  infer_instance

end FLT.Mazur.WeierstrassDividedDepth
