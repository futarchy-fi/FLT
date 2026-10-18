/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRevisedPolygon
public import FLT.Mazur.PolygonVariableSmoothingIdentifiedBase

/-!
# Coefficient projections of every full revised polygon chart

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

local notation "B" => arithmeticRevisedPolygonToBase data H m j hj u hu

/-- Every full node in the revised target preserves the actual coefficient base. -/
@[reassoc] theorem arithmeticRevisedPolygonChart_base (i : Fin N) :
    arithmeticRevisedPolygonChart data H m j hj u hu i ≫ B = chartStructure Q (p i) :=
  PolygonVariableSmoothing.chart_toBase Q N p (by omega) i

/-- The retained chart's parameter identification preserves its coefficient projection. -/
@[reassoc] theorem arithmeticRevisedPolygonRetainedChart_base (idx : Fin (j + 1)) (b : Bool) :
    arithmeticRevisedPolygonRetainedChart data H m j hj u hu idx b ≫ B = chartStructure Q τ :=
  PolygonVariableSmoothing.chartWithParameter_toBase Q N p (by omega)
    (retainedPolygonIndex (j + 1) idx b) τ
    (arithmeticRevisedPolygonParameter_retained data H m j hj u hu idx b).symm

/-- Both complete initial target nodes retain the original arithmetic base. -/
@[reassoc] theorem arithmeticRevisedPolygonInitialChart_base (b : Bool) :
    arithmeticRevisedPolygonInitialChart data H m j hj u hu b ≫ B = chartStructure Q τ :=
  PolygonVariableSmoothing.chartWithParameter_toBase Q N p (by omega)
    (initialPolygonIndex (j + 1) b) τ
    (arithmeticRevisedPolygonParameter_initial data H m j hj u hu b).symm

/-- The full terminal node preserves the base with its actual changed smoothing. -/
@[reassoc] theorem arithmeticRevisedPolygonTerminalChart_base :
    arithmeticRevisedPolygonTerminalChart data H m j hj u hu ≫ B = chartStructure Q σ :=
  PolygonVariableSmoothing.chartWithParameter_toBase Q N p (by omega) 0 σ
    (arithmeticRevisedPolygonParameter_terminal data H m j hj u hu).symm

end FLT.Mazur.WeierstrassDividedDepth
