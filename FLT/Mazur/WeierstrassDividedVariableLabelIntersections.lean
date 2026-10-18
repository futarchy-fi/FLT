/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPolygonTerminalIntersection
public import FLT.Mazur.PolygonVariableSmoothingIdentifiedIntersections

/-!
# Label restrictions for variable-smoothing target intersections

The full target charts keep their cyclic labels even when the terminal
smoothing differs. Opposite initial labels cannot meet the same retained point.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonVariableSmoothing.chartWithParameter
  PolygonVariableSmoothing.scheme
variable (R : Type*) [CommRing R] (k : ℕ) (t : Fin (2 * k + 3) → R)
  [∀ i, Fact (IsNilpotent (t i))]
local notation "c" => PolygonVariableSmoothing.chartWithParameter R (2 * k + 3) t (by omega)

/-- Initial and retained target nodes can meet only on the first edge of the same arm. -/
theorem variableInitial_retained_labels (τ ρ : R) (a : Fin k) (b d : Bool)
    (hi : τ = t (initialPolygonIndex k b)) (hr : ρ = t (retainedPolygonIndex k a d))
    (x : PolygonSmoothing.chart R τ) (y : PolygonSmoothing.chart R ρ)
    (h : c (initialPolygonIndex k b) τ hi x = c (retainedPolygonIndex k a d) ρ hr y) :
    a.val = 0 ∧ b = d := by
  rcases (PolygonVariableSmoothing.identifiedCharts_eq_iff R (2 * k + 3) t (by omega)
    (initialPolygonIndex_ne_retained k a b d) τ ρ hi hr x y).mp h with
    ⟨_, hz, _⟩ | ⟨_, hz, _⟩
  · have hbd := (initialPolygonIndex_preceding_retained_iff k a b d).mp hz
    exact ⟨hbd.2.2, hbd.1.trans hbd.2.1.symm⟩
  · have hbd := (retainedPolygonIndex_preceding_initial_iff k a b d).mp hz
    exact ⟨hbd.2.2, hbd.1.trans hbd.2.1.symm⟩

/-- Only the final retained depth can meet the full terminal node. -/
theorem variableRetained_terminal_location (τ σ : R) (a : Fin k) (b : Bool)
    (hr : τ = t (retainedPolygonIndex k a b)) (ht : σ = t 0)
    (x : PolygonSmoothing.chart R τ) (y : PolygonSmoothing.chart R σ)
    (h : c (retainedPolygonIndex k a b) τ hr x = c 0 σ ht y) : a.val + 1 = k := by
  rcases (PolygonVariableSmoothing.identifiedCharts_eq_iff R (2 * k + 3) t (by omega)
    (retainedPolygonIndex_ne_zero k a b) τ σ hr ht x y).mp h with
    ⟨_, hz, _⟩ | ⟨_, hz, _⟩
  · exact ((retainedPolygonIndex_preceding_zero_iff k a b).mp hz).2
  · exact ((zero_preceding_retainedPolygonIndex_iff k a b).mp hz).2

/-- With a nonempty retained arm, initial and terminal nodes are disjoint in the full target. -/
theorem variableInitial_terminal_ne (hk : 0 < k) (τ σ : R) (b : Bool)
    (hi : τ = t (initialPolygonIndex k b)) (ht : σ = t 0)
    (x : PolygonSmoothing.chart R τ) (y : PolygonSmoothing.chart R σ) :
    c (initialPolygonIndex k b) τ hi x ≠ c 0 σ ht y := by
  intro he
  rcases (PolygonVariableSmoothing.identifiedCharts_eq_iff R (2 * k + 3) t (by omega)
    (initialPolygonIndex_ne_terminal k b) τ σ hi ht x y).mp he with
    ⟨_, hz, _⟩ | ⟨_, hz, _⟩
  · exact initialPolygonIndex_preceding_ne_zero k hk b hz
  · exact zero_preceding_ne_initialPolygonIndex k hk b hz

end FLT.Mazur.WeierstrassDividedDepth
