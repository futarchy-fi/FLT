/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonVariableSmoothingAtlas

/-!
# Exact intersections in a polygon with varying smoothings

Distinct full node charts meet only on their two possible cyclic Laurent edges.
Both edges are retained when the cyclic target has two nodes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.PolygonVariableSmoothing

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open PolygonSmoothing
open PolygonCyclicAtlas (shape)

variable (R : Type u) [CommRing R] (n : ℕ) (t : Fin n → R) [∀ i, Fact (IsNilpotent (t i))]

variable (h : 2 ≤ n)

/-- Distinct node charts intersect precisely along their two possible cyclic edges. -/
theorem charts_eq_iff {i j : Fin n} (hne : i ≠ j)
    (x : PolygonSmoothing.chart R (t i)) (y : PolygonSmoothing.chart R (t j)) :
    chart R n t h i x = chart R n t h j y ↔
      (∃ z : branchTorus R, (finRotate n).symm i = j ∧
        leftBranchOpen R (t i) z = x ∧
        precedingBranch R (t j) z = y) ∨
      (∃ z : branchTorus R, (finRotate n).symm j = i ∧
        precedingBranch R (t i) z = x ∧
        leftBranchOpen R (t j) z = y) := by
  let : Fact (2 ≤ n) := ⟨h⟩
  constructor
  · intro he
    obtain ⟨k, fi, fj, z, hx, hy⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff (diagram R n t)).mp he
    cases fi with
    | id _ =>
      cases fj
      exact (hne rfl).elim
    | fst a =>
      cases fj with
      | fst _ => exact (hne rfl).elim
      | snd _ => exact Or.inl ⟨z, rfl, hx, hy⟩
    | snd a =>
      cases fj with
      | fst _ => exact Or.inr ⟨z, rfl, hx, hy⟩
      | snd _ => exact (hne rfl).elim
  · rintro (⟨z, rfl, rfl, rfl⟩ | ⟨z, rfl, rfl, rfl⟩)
    · exact congrArg (fun f ↦ f z) (overlap R n t h i)
    · exact (congrArg (fun f ↦ f z) (overlap R n t h j)).symm

end FLT.Mazur.PolygonVariableSmoothing
