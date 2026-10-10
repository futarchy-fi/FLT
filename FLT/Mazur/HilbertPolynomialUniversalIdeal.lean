/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertPolynomialAmbientCover
public import FLT.Mazur.HilbertPolynomialAmbientOverlap
public import FLT.Mazur.ClosedIdealCoverGluing

/-!
# The global universal ideal in the polynomial Hilbert ambient space

The compatible actual chart ideals glue to a closed subscheme of the actual
ambient fiber product. Its kernel is the global universal ideal, and pulling
that ideal back to each original polynomial chart recovers the chart ideal.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] (I : Type u) (d : ℕ)

/-- The actual gluing data for the universal closed families on the polynomial charts. -/
def polynomialUniversalClosedGlueData : Scheme.GlueData :=
  ClosedIdealCover.glueData (polynomialHilbertAmbientCover R I d)
    (chartPolynomialIdealSheaf R I d) (chartPolynomialIdealSheaf_pullbackOverlap R I d)

/-- The actual globally glued universal closed family. -/
def polynomialUniversalClosedFamily : Scheme.{u} :=
  (polynomialUniversalClosedGlueData R I d).glued

/-- The global universal family is immersed in the actual polynomial ambient space. -/
def polynomialUniversalClosedImmersion :
    polynomialUniversalClosedFamily R I d ⟶ polynomialHilbertAmbient R I d :=
  ClosedIdealCover.toBase (polynomialHilbertAmbientCover R I d)
    (chartPolynomialIdealSheaf R I d) (chartPolynomialIdealSheaf_pullbackOverlap R I d)

/-- The glued universal family is an actual closed subscheme of the ambient space. -/
instance polynomialUniversalClosedImmersion_isClosedImmersion :
    IsClosedImmersion (polynomialUniversalClosedImmersion R I d) :=
  inferInstanceAs (IsClosedImmersion (ClosedIdealCover.toBase
    (polynomialHilbertAmbientCover R I d) (chartPolynomialIdealSheaf R I d)
    (chartPolynomialIdealSheaf_pullbackOverlap R I d)))

/-- The actual universal ideal on the ambient space over the polynomial Hilbert scheme. -/
def polynomialUniversalIdeal : (polynomialHilbertAmbient R I d).IdealSheafData :=
  (polynomialUniversalClosedImmersion R I d).ker

/-- Pullback to each original polynomial chart recovers its full universal ideal. -/
theorem polynomialUniversalIdeal_chart (w : Fin d → MvPolynomial I R) :
    (polynomialUniversalIdeal R I d).comap (polynomialHilbertAmbientChart R I d w) =
      chartPolynomialIdealSheaf R I d w :=
  ClosedIdealCover.ker_toBase_comap (polynomialHilbertAmbientCover R I d)
    (chartPolynomialIdealSheaf R I d) (chartPolynomialIdealSheaf_pullbackOverlap R I d) w

/-- The original closed chart family is the actual pullback of the global closed family. -/
theorem polynomialUniversalClosedFamily_chart (w : Fin d → MvPolynomial I R) :
    IsPullback (chartPolynomialIdealSheaf R I d w).subschemeι
      ((polynomialUniversalClosedGlueData R I d).ι w)
      (polynomialHilbertAmbientChart R I d w) (polynomialUniversalClosedImmersion R I d) :=
  ClosedIdealCover.chart_isPullback (polynomialHilbertAmbientCover R I d)
    (chartPolynomialIdealSheaf R I d) (chartPolynomialIdealSheaf_pullbackOverlap R I d) w

end FLT.Mazur.HilbertChart
