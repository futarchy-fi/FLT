/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertAmbientRelationOverlap
public import FLT.Mazur.ClosedIdealCoverGluing

/-!
# The actual closed ambient Hilbert parameter scheme

The full compatible equation sheaves glue to a closed subscheme of the
polynomial Hilbert scheme. Each original closed ambient chart is its actual
cartesian restriction, without any finiteness assumption on the relations.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R] (d : ℕ)
variable (K : Ideal (MvPolynomial I R))

/-- Actual gluing data for the closed ambient parameter charts. -/
def ambientHilbertGlueData : Scheme.GlueData :=
  ClosedIdealCover.glueData (polynomialHilbertSchemeCover R I d)
    (ambientRelationsSheaf R I d K) (ambientRelationsSheaf_pullbackOverlap R I d K)

/-- The actual parameter scheme imposing all ambient relations. -/
def ambientHilbertScheme : Scheme.{u} := (ambientHilbertGlueData R I d K).glued

/-- The closed ambient parameter scheme sits inside the polynomial Hilbert scheme. -/
def ambientHilbertι : ambientHilbertScheme R I d K ⟶ polynomialHilbertScheme R I d :=
  ClosedIdealCover.toBase (polynomialHilbertSchemeCover R I d)
    (ambientRelationsSheaf R I d K) (ambientRelationsSheaf_pullbackOverlap R I d K)

/-- The glued ambient parameter map is an actual closed immersion. -/
instance ambientHilbertι_isClosedImmersion : IsClosedImmersion (ambientHilbertι R I d K) :=
  inferInstanceAs (IsClosedImmersion (ClosedIdealCover.toBase
    (polynomialHilbertSchemeCover R I d) (ambientRelationsSheaf R I d K)
    (ambientRelationsSheaf_pullbackOverlap R I d K)))

/-- The ambient parameter scheme lies over the original coefficient spectrum. -/
def ambientHilbertStructure : ambientHilbertScheme R I d K ⟶ Spec (.of R) :=
  ambientHilbertι R I d K ≫ polynomialHilbertStructure R I d

/-- The full global equation ideal of the ambient parameter scheme. -/
def ambientHilbertIdeal : (polynomialHilbertScheme R I d).IdealSheafData :=
  (ambientHilbertι R I d K).ker

/-- Restricting the global equation ideal recovers every original coordinate equation. -/
theorem ambientHilbertIdeal_chart (w : Fin d → MvPolynomial I R) :
    (ambientHilbertIdeal R I d K).comap (polynomialHilbertChartι R I d w) =
      ambientRelationsSheaf R I d K w :=
  ClosedIdealCover.ker_toBase_comap (polynomialHilbertSchemeCover R I d)
    (ambientRelationsSheaf R I d K) (ambientRelationsSheaf_pullbackOverlap R I d K) w

/-- Each closed parameter chart is exactly the base change of the global closed scheme. -/
theorem ambientHilbert_chart_isPullback (w : Fin d → MvPolynomial I R) :
    IsPullback (ambientRelationsSheaf R I d K w).subschemeι
      ((ambientHilbertGlueData R I d K).ι w)
      (polynomialHilbertChartι R I d w) (ambientHilbertι R I d K) :=
  ClosedIdealCover.chart_isPullback (polynomialHilbertSchemeCover R I d)
    (ambientRelationsSheaf R I d K) (ambientRelationsSheaf_pullbackOverlap R I d K) w

end FLT.Mazur.HilbertChart
