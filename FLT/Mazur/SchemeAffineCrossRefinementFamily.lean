/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineCrossRefinementQuasicoherent

/-!
# Simultaneous geometric cross refinements of a family of affine charts

A common affine base and faithfully flat cover retain one independent covering
map for every original chart. Each pair gives an existing cross refinement,
and all refined charts use the same named base map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u v
namespace FLT.Mazur.SchemeAffineDescent.Chart
variable {X Y : Scheme.{u}} {p : Y ⟶ X} {ι : Type v} (C : ι → Chart p)

/-- Geometric data for simultaneous cross refinements, without any sheaf comparison fields. -/
structure CrossRefinementFamily where
  /-- Coordinate ring of the common base. -/
  baseRing : CommRingCat.{u}
  /-- Coordinate ring of the common cover. -/
  coverRing : CommRingCat.{u}
  /-- Faithfully flat covering map in ring coordinates. -/
  ringMap : baseRing ⟶ coverRing
  /-- Faithful flatness of the common cover. -/
  faithfullyFlat : ringMap.hom.FaithfullyFlat
  /-- The single named map into the original base scheme. -/
  base : Spec baseRing ⟶ X
  /-- Coordinates in each original base chart. -/
  baseMap (i : ι) : (C i).baseRing ⟶ baseRing
  /-- Independent coordinates in each original covering chart. -/
  coverMap (i : ι) : (C i).coverRing ⟶ coverRing
  /-- Every affine square commutes. -/
  square (i : ι) : (C i).ringMap ≫ coverMap i = baseMap i ≫ ringMap
  /-- Every original base path has the same target map. -/
  base_over (i : ι) : Spec.map (baseMap i) ≫ (C i).base = base

namespace CrossRefinementFamily
variable {C} (ρ : CrossRefinementFamily C)

/-- Any two members yield the existing geometric cross-refinement data. -/
def pair (i j : ι) : (C i).CrossRefinement (C j) where
  baseRing := ρ.baseRing
  coverRing := ρ.coverRing
  ringMap := ρ.ringMap
  faithfullyFlat := ρ.faithfullyFlat
  leftBase := ρ.baseMap i
  rightBase := ρ.baseMap j
  leftCover := ρ.coverMap i
  rightCover := ρ.coverMap j
  leftSquare := ρ.square i
  rightSquare := ρ.square j
  base_over := (ρ.base_over i).trans (ρ.base_over j).symm

/-- The independent map of the common cover into the original covering scheme. -/
def cover (i : ι) : Spec ρ.coverRing ⟶ Y :=
  Spec.map (ρ.coverMap i) ≫ (C i).cover

/-- The common cover square for each original chart. -/
theorem cover_square (i : ι) : Spec.map ρ.ringMap ≫ ρ.base = ρ.cover i ≫ p := by
  rw [← ρ.base_over i]
  exact SchemeGeometricDescent.Data.affineChart_composite_square
    (C i).ringMap ρ.ringMap (ρ.baseMap i) (ρ.coverMap i) (ρ.square i)
    p (C i).base (C i).cover (C i).square

/-- Refine each original chart while keeping the same named base map. -/
def chart (i : ι) : Chart p where
  baseRing := ρ.baseRing
  coverRing := ρ.coverRing
  ringMap := ρ.ringMap
  faithfullyFlat := ρ.faithfullyFlat
  base := ρ.base
  cover := ρ.cover i
  square := ρ.cover_square i

/-- The geometric refinement into each common chart. -/
def refinement (i : ι) : (C i).Refinement (ρ.chart i) where
  base := ρ.baseMap i
  cover := ρ.coverMap i
  square := ρ.square i
  base_over := ρ.base_over i
  cover_over := rfl

/-- Common-chart pullbacks inherit quasicoherence from the original covering chart. -/
instance chart_isQuasicoherent (i : ι) {M : Y.Modules}
    [((pullback (C i).cover).obj M).IsQuasicoherent] :
    ((pullback (ρ.chart i).cover).obj M).IsQuasicoherent :=
  SchemeGeometricDescent.Data.isQuasicoherent_compositeChartPullback
    (ρ.coverMap i) (C i).cover

end CrossRefinementFamily
end FLT.Mazur.SchemeAffineDescent.Chart
