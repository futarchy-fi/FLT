/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteLocallyFreeDegreeCover
public import FLT.Mazur.HilbertPolynomialUniversalIdeal
public import FLT.Mazur.BaseAdicQuotientSpectrum

/-!
# Finite locally free degree of each universal polynomial chart

The closed universal chart is the spectrum of its actual polynomial quotient.
Its explicit prescribed basis proves finite locally free degree `d`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FLT.Mazur.BaseAdicThickening FLT.Mazur.FCurve

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] (I : Type u) (d : ℕ)
variable (w : Fin d → MvPolynomial I R)

/-- Cache coefficients for the closed chart's quotient. -/
local instance degreeCoefficientsRing : CommRing (Coefficients R I d) := inferInstance
/-- Cache the parameter ring for the closed chart's quotient. -/
local instance degreeChartRing : CommRing (ChartRing R I d w) := inferInstance

attribute [local irreducible] chartIdentityIdeal

/-- The closed universal chart projects to its parameter chart. -/
def chartPolynomialClosedProjection : (chartPolynomialIdealSheaf R I d w).subscheme ⟶
    Spec (.of (ChartRing R I d w)) :=
  (chartPolynomialIdealSheaf R I d w).subschemeι ≫ chartPolynomialProjection R I d w

/-- The actual closed chart is the spectrum of the original universal polynomial quotient. -/
def chartPolynomialQuotientIso :
    Spec (.of (MvPolynomial I (ChartRing R I d w) ⧸ chartIdentityIdeal R I d w)) ≅
      (chartPolynomialIdealSheaf R I d w).subscheme :=
  quotientSpecIso (.of (MvPolynomial I (ChartRing R I d w))) (chartIdentityIdeal R I d w)

/-- The quotient comparison preserves the actual parameter projection. -/
@[reassoc]
theorem chartPolynomialQuotientIso_hom_projection :
    (chartPolynomialQuotientIso R I d w).hom ≫ chartPolynomialClosedProjection R I d w =
      Spec.map (CommRingCat.ofHom (algebraMap (ChartRing R I d w)
        (MvPolynomial I (ChartRing R I d w) ⧸ chartIdentityIdeal R I d w))) := by
  rw [chartPolynomialClosedProjection, ← Category.assoc]
  change ((quotientSpecIso (.of (MvPolynomial I (ChartRing R I d w)))
    (chartIdentityIdeal R I d w)).hom ≫ (baseIdeal _ _).subschemeι) ≫ _ = _
  rw [quotientSpecIso_hom_ι, chartPolynomialProjection, ← Spec.map_comp]
  rfl

/-- The closed universal chart is finite locally free of exactly the prescribed degree. -/
theorem chartPolynomialClosedProjection_degree :
    FiniteLocallyFreeDegree (chartPolynomialClosedProjection R I d w) d := by
  let e : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap (ChartRing R I d w)
      (MvPolynomial I (ChartRing R I d w) ⧸ chartIdentityIdeal R I d w)))) ≅
      Over.mk (chartPolynomialClosedProjection R I d w) := by
    refine Over.isoMk (chartPolynomialQuotientIso R I d w) ?_
    exact chartPolynomialQuotientIso_hom_projection R I d w
  exact (finiteLocallyFreeDegree_iff_of_overIso e).mp
    (finiteLocallyFreeDegree_spec_of_basis _ _ d (chartIdentityBasis R I d w))

end FLT.Mazur.HilbertChart
