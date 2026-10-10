/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.MultiplicativeGroupDimension
public import FLT.Mazur.PolygonInfinitesimalStages
public import FLT.Mazur.SmoothOpenSectionCartier

/-!
# Cartier markings on the actual infinitesimal polygon

The Laurent marking neighborhoods have relative dimension one. Smooth section
Cartier theory therefore applies to the actual globally glued marked sections,
including over nonreduced coefficient rings.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.PolygonInfinitesimal

open PolygonSmoothing FCurve

variable (R : Type u) [CommRing R] (t : R) [Fact (IsNilpotent t)]
  (n : ℕ) (h : 2 ≤ n)

/-- The full Laurent neighborhood of each marking is a smooth relative curve. -/
instance marking_open_dimension (i : Fin n) :
    SmoothOfRelativeDimension 1
      ((leftBranchOpen R t ≫ chart R t n h i) ≫ toBase R t n h) := by
  rw [Category.assoc, chart_toBase, leftBranchOpen_base]
  exact MultiplicativeGroupDimension.dimension R

/-- Every specified unit marking gives its actual relative Cartier section ideal. -/
theorem marking_cartier (i : Fin n) (a : Rˣ) :
    RelativeEffectiveCartier (toBase R t n h) (marking R t n h i a).ker := by
  let _ := PolygonInfinitesimalSeparated.separated R t n h
  have he : markedTorusSection a ≫ (leftBranchOpen R t ≫ chart R t n h i) =
      marking R t n h i a := by
    rw [← Category.assoc, markedTorusSection_left, marking]
  have hs : markedTorusSection a ≫
      (leftBranchOpen R t ≫ chart R t n h i) ≫ toBase R t n h = 𝟙 _ := by
    rw [← Category.assoc, he, marking_base]
  have hc := smoothOpenSectionCartier (leftBranchOpen R t ≫ chart R t n h i)
    (toBase R t n h) (markedTorusSection a) inferInstance inferInstance inferInstance hs
  rwa [he] at hc

end FLT.Mazur.PolygonInfinitesimal
