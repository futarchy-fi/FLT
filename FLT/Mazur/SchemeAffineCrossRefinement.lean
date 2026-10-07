/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineChartReconstruction
public import FLT.Mazur.SchemeCrossCoverOverlap

/-!
# Affine refinements with two independent maps into the covering scheme

A cross refinement has one affine base and one faithfully flat affine cover,
but two maps to the original covering charts. Only their base maps agree.
It gives two genuine chart refinements, keeping the cover maps independent.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeAffineDescent.Chart
variable {X Y : Scheme.{u}} {p : Y ⟶ X} (C C' : Chart p)

/-- Pure geometric inputs for comparing two charts over a common affine base. -/
structure CrossRefinement where
  /-- Ring of the common base. -/
  baseRing : CommRingCat.{u}
  /-- Ring of its chosen affine cover. -/
  coverRing : CommRingCat.{u}
  /-- The faithfully flat affine cover map. -/
  ringMap : baseRing ⟶ coverRing
  /-- Faithful flatness of the chosen cover. -/
  faithfullyFlat : ringMap.hom.FaithfullyFlat
  /-- Restriction of the first base chart. -/
  leftBase : C.baseRing ⟶ baseRing
  /-- Restriction of the second base chart. -/
  rightBase : C'.baseRing ⟶ baseRing
  /-- Map to the first covering chart. -/
  leftCover : C.coverRing ⟶ coverRing
  /-- Map to the second covering chart. -/
  rightCover : C'.coverRing ⟶ coverRing
  /-- The first ring square commutes. -/
  leftSquare : C.ringMap ≫ leftCover = leftBase ≫ ringMap
  /-- The second ring square commutes. -/
  rightSquare : C'.ringMap ≫ rightCover = rightBase ≫ ringMap
  /-- The two base paths agree over the original base scheme. -/
  base_over : Spec.map leftBase ≫ C.base = Spec.map rightBase ≫ C'.base

namespace CrossRefinement
variable {C C'} (ρ : C.CrossRefinement C')

/-- The common affine chart with the first map into the original cover. -/
def leftChart : Chart p where
  baseRing := ρ.baseRing
  coverRing := ρ.coverRing
  ringMap := ρ.ringMap
  faithfullyFlat := ρ.faithfullyFlat
  base := Spec.map ρ.leftBase ≫ C.base
  cover := Spec.map ρ.leftCover ≫ C.cover
  square := SchemeGeometricDescent.Data.affineChart_composite_square
    C.ringMap ρ.ringMap ρ.leftBase ρ.leftCover ρ.leftSquare p C.base C.cover C.square

/-- The same affine base and cover with the second map into the original cover. -/
def rightChart : Chart p where
  baseRing := ρ.baseRing
  coverRing := ρ.coverRing
  ringMap := ρ.ringMap
  faithfullyFlat := ρ.faithfullyFlat
  base := Spec.map ρ.leftBase ≫ C.base
  cover := Spec.map ρ.rightCover ≫ C'.cover
  square := by
    rw [ρ.base_over]
    exact SchemeGeometricDescent.Data.affineChart_composite_square
      C'.ringMap ρ.ringMap ρ.rightBase ρ.rightCover ρ.rightSquare p
      C'.base C'.cover C'.square

/-- Genuine refinement from the first chart, preserving its map into the cover. -/
def leftRefinement : C.Refinement ρ.leftChart where
  base := ρ.leftBase
  cover := ρ.leftCover
  square := ρ.leftSquare
  base_over := rfl
  cover_over := rfl

/-- Genuine refinement from the second chart, preserving its separate cover map. -/
def rightRefinement : C'.Refinement ρ.rightChart where
  base := ρ.rightBase
  cover := ρ.rightCover
  square := ρ.rightSquare
  base_over := ρ.base_over.symm
  cover_over := rfl

/-- The two covering maps coincide after mapping to the original base. -/
theorem covers_over : ρ.leftChart.cover ≫ p = ρ.rightChart.cover ≫ p :=
  ρ.leftChart.square.symm.trans ρ.rightChart.square

/-- The common affine cover maps to the product of the original covering charts over X. -/
def coverPair : Spec ρ.coverRing ⟶ SchemeCrossCoverOverlap.product p C.cover C'.cover :=
  Limits.pullback.lift (Spec.map ρ.leftCover) (Spec.map ρ.rightCover) (by
    simpa only [leftChart, rightChart, Category.assoc] using ρ.covers_over)

/-- The cross-cover product map retains the first original covering-chart projection. -/
@[reassoc (attr := simp)]
theorem coverPair_fst :
    ρ.coverPair ≫ Limits.pullback.fst (C.cover ≫ p) (C'.cover ≫ p) =
      Spec.map ρ.leftCover := Limits.pullback.lift_fst _ _ _

/-- The cross-cover product map retains the second original covering-chart projection. -/
@[reassoc (attr := simp)]
theorem coverPair_snd :
    ρ.coverPair ≫ Limits.pullback.snd (C.cover ≫ p) (C'.cover ≫ p) =
      Spec.map ρ.rightCover := Limits.pullback.lift_snd _ _ _

end CrossRefinement
end FLT.Mazur.SchemeAffineDescent.Chart
