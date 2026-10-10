/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonInfinitesimalDiagram

/-!
# Actual cyclic schemes at nilpotent smoothing parameters

Glue the full arithmetic smoothing charts for n ≥ 2. The open chart maps cover
the resulting scheme and their complete intersection relation retains both
edges for the two-gon. Nilpotence is used by the diagram's gluing cocycle.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.PolygonInfinitesimal

open PolygonSmoothing
open PolygonCyclicAtlas (shape)

variable (R : Type u) [CommRing R] (t : R) [Fact (IsNilpotent t)] (n : ℕ)

variable (h : 2 ≤ n)

/-- The scheme obtained by gluing the cyclic node charts. -/
def scheme : Scheme.{u} :=
  letI : Fact (2 ≤ n) := ⟨h⟩
  colimit (diagram R t n)

/-- The inclusion of a node chart. -/
def chart (i : Fin n) : PolygonSmoothing.chart R t ⟶ scheme R t n h :=
  letI : Fact (2 ≤ n) := ⟨h⟩
  colimit.ι (diagram R t n) (.right i)

instance chart_isOpenImmersion (i : Fin n) : IsOpenImmersion (chart R t n h i) := by
  let : Fact (2 ≤ n) := ⟨h⟩
  exact inferInstanceAs (IsOpenImmersion (colimit.ι (diagram R t n) (.right i)))

/-- The two coordinate inclusions of an edge agree in the glued scheme. -/
@[reassoc]
theorem overlap (i : Fin n) :
    leftBranchOpen R t ≫ chart R t n h i =
      precedingBranch R t ≫
        chart R t n h ((finRotate n).symm i) := by
  let : Fact (2 ≤ n) := ⟨h⟩
  exact (colimit.w (diagram R t n) (WalkingMultispan.Hom.fst i)).trans
    (colimit.w (diagram R t n) (WalkingMultispan.Hom.snd i)).symm

/-- The node charts cover the scheme; the edges add no extra points. -/
theorem charts_cover (x : scheme R t n h) : ∃ i y, chart R t n h i y = x := by
  let : Fact (2 ≤ n) := ⟨h⟩
  obtain ⟨j, y, hy⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (diagram R t n) x
  cases j with
  | right i => exact ⟨i, y, hy⟩
  | left i =>
    refine ⟨i, leftBranchOpen R t y, ?_⟩
    change ((diagram R t n).map (WalkingMultispan.Hom.fst i) ≫
      colimit.ι (diagram R t n) (.right i)) y = x
    exact (congrArg (fun f ↦ f y)
      (colimit.w (diagram R t n) (WalkingMultispan.Hom.fst i))).trans hy

/-- Distinct node charts intersect precisely along their two possible cyclic edges. -/
theorem charts_eq_iff {i j : Fin n} (hne : i ≠ j)
    (x y : PolygonSmoothing.chart R t) :
    chart R t n h i x = chart R t n h j y ↔
      (∃ z : branchTorus R, (finRotate n).symm i = j ∧
        leftBranchOpen R t z = x ∧
        (precedingBranch R t) z = y) ∨
      (∃ z : branchTorus R, (finRotate n).symm j = i ∧
        (precedingBranch R t) z = x ∧
        leftBranchOpen R t z = y) := by
  let : Fact (2 ≤ n) := ⟨h⟩
  constructor
  · intro he
    obtain ⟨k, fi, fj, z, hx, hy⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff (diagram R t n)).mp he
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
    · exact congrArg (fun f ↦ f z) (overlap R t n h i)
    · exact (congrArg (fun f ↦ f z) (overlap R t n h j)).symm

/-- Both cyclic edges occur in the intersection of the two charts of the two-gon. -/
theorem two_charts_eq_iff (x y : PolygonSmoothing.chart R t) :
    chart R t 2 (by decide) 0 x = chart R t 2 (by decide) 1 y ↔
      (∃ z : branchTorus R, leftBranchOpen R t z = x ∧
        (precedingBranch R t) z = y) ∨
      (∃ z : branchTorus R,
        (precedingBranch R t) z = x ∧
        leftBranchOpen R t z = y) := by
  simpa only [show (finRotate 2).symm 0 = 1 from by decide,
    show (finRotate 2).symm 1 = 0 from by decide, true_and] using
      charts_eq_iff R t 2 (by decide) (i := 0) (j := 1) (by decide) x y


end FLT.Mazur.PolygonInfinitesimal
