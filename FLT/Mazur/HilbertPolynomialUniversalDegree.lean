/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertPolynomialChartDegree

/-!
# Finite locally free degree of the global universal polynomial family

The actual closed universal family projects to the glued Hilbert scheme.
Its original closed charts are cartesian over the parameter cover, so their
explicit quotient bases prove finite locally free degree everywhere.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FLT.Mazur.FCurve

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] (I : Type u) (d : ℕ)

/-- The actual universal closed family projects to its Hilbert parameter scheme. -/
def polynomialUniversalProjection :
    polynomialUniversalClosedFamily R I d ⟶ polynomialHilbertScheme R I d :=
  polynomialUniversalClosedImmersion R I d ≫ pullback.fst _ _

/-- Each original closed chart is the inverse image of its parameter chart. -/
theorem polynomialUniversalProjection_chart (w : Fin d → MvPolynomial I R) :
    IsPullback ((polynomialUniversalClosedGlueData R I d).ι w)
      (chartPolynomialClosedProjection R I d w)
      (polynomialUniversalProjection R I d) (polynomialHilbertChartι R I d w) := by
  exact (polynomialUniversalClosedFamily_chart R I d w).flip.paste_vert
    (polynomialHilbertAmbientChart_isPullback R I d w)

/-- The universal polynomial family is finite locally free of exactly rank `d`. -/
theorem polynomialUniversalProjection_degree :
    FiniteLocallyFreeDegree (polynomialUniversalProjection R I d) d :=
  finiteLocallyFreeDegree_of_cartesianCover (polynomialUniversalProjection R I d)
    (polynomialHilbertSchemeCover R I d)
    (fun w ↦ (chartPolynomialIdealSheaf R I d w).subscheme)
    (fun w ↦ (polynomialUniversalClosedGlueData R I d).ι w)
    (chartPolynomialClosedProjection R I d) (polynomialUniversalProjection_chart R I d) d
    (chartPolynomialClosedProjection_degree R I d)

/-- The universal projection has finite fibers scheme-theoretically. -/
instance polynomialUniversalProjection_isFinite : IsFinite (polynomialUniversalProjection R I d) :=
  (polynomialUniversalProjection_degree R I d).1

/-- The universal family is flat over the entire glued parameter scheme. -/
instance polynomialUniversalProjection_flat : Flat (polynomialUniversalProjection R I d) :=
  (polynomialUniversalProjection_degree R I d).2.1

/-- The universal projection is locally of finite presentation. -/
instance polynomialUniversalProjection_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (polynomialUniversalProjection R I d) :=
  (polynomialUniversalProjection_degree R I d).2.2.1

/-- The universal family has the prescribed rank at every parameter point. -/
theorem polynomialUniversalProjection_finrank (x : polynomialHilbertScheme R I d) :
    (polynomialUniversalProjection R I d).finrank x = d :=
  (polynomialUniversalProjection_degree R I d).2.2.2 x

end FLT.Mazur.HilbertChart
