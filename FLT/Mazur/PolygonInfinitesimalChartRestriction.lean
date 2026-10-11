/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingRingMap
public import FLT.Mazur.PolygonInfinitesimalStageRestriction

/-!
# Original arithmetic charts under the actual stage restrictions

The explicit polynomial coefficient maps are the chart maps of the existing
glued family projections, including the specified adjacent stage restriction.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.PolygonInfinitesimal

open PolygonSmoothing

set_option backward.isDefEq.respectTransparency false

variable {R S : Type u} [CommRing R] [CommRing S]
  (f : R →+* S) (t : R) (s : S) [Fact (IsNilpotent t)] [Fact (IsNilpotent s)]
  (hs : f t = s) (n : ℕ) (h : 2 ≤ n)

/-- The actual glued projection restricts to the specified original chart ring map. -/
@[reassoc] theorem chart_parameterProjection (i : Fin n) :
    chart S s n h i ≫ parameterProjection f t s hs n h =
      Spec.map (CommRingCat.ofHom (ringMap f t s hs)) ≫ chart R t n h i := by
  subst s
  let _ := f.toAlgebra
  change chart S (algebraMap R S t) n h i ≫ coefficientProjection R S t n h =
    Spec.map (CommRingCat.ofHom
      (ringMap (algebraMap R S) t (algebraMap R S t) rfl)) ≫ chart R t n h i
  rw [ringMap_eq_coefficientMap]
  exact chart_coefficientProjection R S t n h i

end FLT.Mazur.PolygonInfinitesimal

namespace FLT.Mazur.PolygonInfinitesimalStages

open PolygonSmoothing

variable (R : Type u) [CommRing R] (m n : ℕ) (h : 2 ≤ n)

/-- The original adjacent coefficient substitution on the actual chart rings. -/
def stageChartRestriction : ChartRing (parameter R (m + 1)) →+* ChartRing (parameter R m) :=
  ringMap (restriction R m).toRingHom _ _ (restriction_parameter R m)

/-- The stage restriction on every original glued chart is its actual coefficient map. -/
@[reassoc] theorem chart_stageRestriction (i : Fin n) :
    PolygonInfinitesimal.chart (Ring R m) (parameter R m) n h i ≫
      stageRestriction R m n h =
        Spec.map (CommRingCat.ofHom (stageChartRestriction R m)) ≫
          PolygonInfinitesimal.chart (Ring R (m + 1)) (parameter R (m + 1)) n h i :=
  PolygonInfinitesimal.chart_parameterProjection _ _ _ _ _ _ i

/-- The adjacent chart restriction preserves the original node ideal exactly. -/
theorem stageChartRestriction_coordinateIdeal :
    (coordinateIdeal (parameter R (m + 1))).map (stageChartRestriction R m) =
      coordinateIdeal (parameter R m) :=
  ringMap_coordinateIdeal _ _ _ _

end FLT.Mazur.PolygonInfinitesimalStages
