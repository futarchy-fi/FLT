/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRevisedInitialRetainedReflection
public import FLT.Mazur.WeierstrassDividedVariableLabelIntersections

/-!
# Initial and terminal label restrictions in the revised target

The exact cyclic classification is expressed using the named target charts,
so original normalization maps can use it without expanding the target.
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
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "p" => arithmeticRevisedPolygonParameter data H m j hj u hu
local notation "c" => arithmeticRevisedPolygonRetainedChart data H m j hj u hu
local notation "O" => twistedRetainedOrientation data H m
attribute [local irreducible] arithmeticRevisedPolygon
  PolygonVariableSmoothing.scheme PolygonVariableSmoothing.chartWithParameter

local notation "σ" => arithmeticTerminalChangedSmoothing data H m j hj u hu
local notation "d" => arithmeticRevisedPolygonTerminalChart data H m j hj u hu
local notation "a" => arithmeticRevisedPolygonInitialChart data H m j hj u hu

/-- Meeting the full terminal node forces the last retained depth at every order. -/
theorem arithmeticRevisedRetainedTerminal_location (idx : Fin (j + 1)) (b : Bool)
    (x : PolygonSmoothing.chart Q τ) (y : PolygonSmoothing.chart Q σ)
    (h : c idx b x = d y) : idx.val = j := by
  have hi := variableRetained_terminal_location Q (j + 1) p τ σ idx b
    (arithmeticRevisedPolygonParameter_retained data H m j hj u hu idx b).symm
    (arithmeticRevisedPolygonParameter_terminal data H m j hj u hu).symm x y (by
      convert h using 1
      unfold arithmeticRevisedPolygon arithmeticRevisedPolygonRetainedChart
        arithmeticRevisedPolygonTerminalChart
      rfl)
  exact Nat.add_right_cancel hi

/-- Initial and retained target nodes meet only on the first edge of the same arm. -/
theorem arithmeticRevisedInitialRetained_labels (idx : Fin (j + 1)) (b e : Bool)
    (x y : PolygonSmoothing.chart Q τ) (h : a b x = c idx e y) : idx.val = 0 ∧ b = e := by
  apply variableInitial_retained_labels Q (j + 1) p τ τ idx b e
    (arithmeticRevisedPolygonParameter_initial data H m j hj u hu b).symm
    (arithmeticRevisedPolygonParameter_retained data H m j hj u hu idx e).symm x y
  convert h using 1
  unfold arithmeticRevisedPolygon arithmeticRevisedPolygonInitialChart
    arithmeticRevisedPolygonRetainedChart
  rfl

/-- The full initial and terminal nodes remain disjoint at every arithmetic order. -/
theorem arithmeticRevisedInitialTerminal_ne (b : Bool)
    (x : PolygonSmoothing.chart Q τ) (y : PolygonSmoothing.chart Q σ) : a b x ≠ d y := by
  intro he
  apply variableInitial_terminal_ne Q (j + 1) p (Nat.zero_lt_succ j) τ σ b
    (arithmeticRevisedPolygonParameter_initial data H m j hj u hu b).symm
    (arithmeticRevisedPolygonParameter_terminal data H m j hj u hu).symm x y
  convert he using 1
  unfold arithmeticRevisedPolygon arithmeticRevisedPolygonInitialChart
    arithmeticRevisedPolygonTerminalChart
  rfl

end FLT.Mazur.WeierstrassDividedDepth
