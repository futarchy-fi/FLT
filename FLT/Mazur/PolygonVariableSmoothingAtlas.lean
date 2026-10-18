/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonVariableSmoothingDiagram

/-!
# Cyclic targets with independent node smoothings

The full charts glue along standard Laurent punctures. The constructed target
has an open cover and a descent map for compatible maps on all its nodes.
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

/-- The scheme obtained by gluing the cyclic node charts. -/
def scheme : Scheme.{u} :=
  letI : Fact (2 ≤ n) := ⟨h⟩
  colimit (diagram R n t)

/-- The inclusion of a node chart. -/
def chart (i : Fin n) : PolygonSmoothing.chart R (t i) ⟶ scheme R n t h :=
  letI : Fact (2 ≤ n) := ⟨h⟩
  colimit.ι (diagram R n t) (.right i)

instance chart_isOpenImmersion (i : Fin n) : IsOpenImmersion (chart R n t h i) := by
  let : Fact (2 ≤ n) := ⟨h⟩
  exact inferInstanceAs (IsOpenImmersion (colimit.ι (diagram R n t) (.right i)))

/-- The two coordinate inclusions of an edge agree in the glued scheme. -/
@[reassoc]
theorem overlap (i : Fin n) :
    leftBranchOpen R (t i) ≫ chart R n t h i =
      precedingBranch R (t ((finRotate n).symm i)) ≫
        chart R n t h ((finRotate n).symm i) := by
  let : Fact (2 ≤ n) := ⟨h⟩
  have hf := colimit.w (diagram R n t) (WalkingMultispan.Hom.fst i)
  have hs := colimit.w (diagram R n t) (WalkingMultispan.Hom.snd i)
  exact hf.trans hs.symm

/-- The node charts cover the scheme; the edges add no extra points. -/
theorem charts_cover (x : scheme R n t h) : ∃ i y, chart R n t h i y = x := by
  let : Fact (2 ≤ n) := ⟨h⟩
  obtain ⟨j, y, hy⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (diagram R n t) x
  cases j with
  | right i => exact ⟨i, y, hy⟩
  | left i =>
    refine ⟨i, leftBranchOpen R (t i) y, ?_⟩
    change ((diagram R n t).map (WalkingMultispan.Hom.fst i) ≫
      colimit.ι (diagram R n t) (.right i)) y = x
    exact (congrArg (fun f ↦ f y)
      (colimit.w (diagram R n t) (WalkingMultispan.Hom.fst i))).trans hy

/-- Compatible maps from the separate full node charts descend to the cyclic target. -/
def desc {Y : Scheme.{u}}
    (f : ∀ i, PolygonSmoothing.chart R (t i) ⟶ Y)
    (hf : ∀ i, leftBranchOpen R (t i) ≫ f i =
      precedingBranch R (t ((finRotate n).symm i)) ≫ f ((finRotate n).symm i)) :
    scheme R n t h ⟶ Y := by
  let _ : Fact (2 ≤ n) := ⟨h⟩
  exact colimit.desc (diagram R n t) (Multicofork.ofπ (index R n t) Y f hf)

/-- Descent retains each full node map. -/
@[reassoc] theorem chart_desc {Y : Scheme.{u}}
    (f : ∀ i, PolygonSmoothing.chart R (t i) ⟶ Y)
    (hf : ∀ i, leftBranchOpen R (t i) ≫ f i =
      precedingBranch R (t ((finRotate n).symm i)) ≫ f ((finRotate n).symm i))
    (i : Fin n) : chart R n t h i ≫ desc R n t h f hf = f i := by
  let _ : Fact (2 ≤ n) := ⟨h⟩
  exact colimit.ι_desc (F := diagram R n t)
    (Multicofork.ofπ (index R n t) Y f hf) (WalkingMultispan.right i)

end FLT.Mazur.PolygonVariableSmoothing
