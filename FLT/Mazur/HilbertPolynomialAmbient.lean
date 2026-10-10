/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertChartIdealSheafTransition
public import FLT.Mazur.HilbertPolynomialSchemeOver
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# The actual polynomial ambient space of the glued Hilbert scheme

The ambient space is the fiber product with affine polynomial space over the
coefficient base. Each chart's polynomial spectrum is its actual base change,
so the chart maps into the ambient space are open immersions.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] (I : Type u) (d : ℕ)
variable (w : Fin d → MvPolynomial I R)

/-- Cache the coefficient ring for polynomial pullback inference. -/
local instance ambientCoefficientsRing : CommRing (Coefficients R I d) := inferInstance
/-- Cache the chart ring for polynomial pullback inference. -/
local instance ambientChartRing : CommRing (ChartRing R I d w) := inferInstance

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- The chart polynomial spectrum is the actual base change of affine polynomial space. -/
theorem chartPolynomial_isPullback :
    IsPullback (chartPolynomialProjection R I d w) (chartPolynomialOriginal R I d w)
      (Spec.map (CommRingCat.ofHom (algebraMap R (ChartRing R I d w))))
      (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial I R)))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isPushout R (ChartRing R I d w)
      (MvPolynomial I R) (MvPolynomial I (ChartRing R I d w)))

/-- The actual ambient polynomial space over the glued parameter scheme. -/
def polynomialHilbertAmbient : Scheme.{u} :=
  pullback (polynomialHilbertStructure R I d)
    (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial I R))))

/-- The polynomial spectrum over a parameter chart maps into the global ambient space. -/
def polynomialHilbertAmbientChart :
    Spec (.of (MvPolynomial I (ChartRing R I d w))) ⟶ polynomialHilbertAmbient R I d :=
  pullback.lift (chartPolynomialProjection R I d w ≫ polynomialHilbertChartι R I d w)
    (chartPolynomialOriginal R I d w) (by
      rw [Category.assoc, polynomialHilbertChartι_over]
      exact (chartPolynomial_isPullback R I d w).w)

/-- The ambient chart retains its original parameter projection. -/
@[reassoc]
theorem polynomialHilbertAmbientChart_fst :
    polynomialHilbertAmbientChart R I d w ≫ pullback.fst _ _ =
      chartPolynomialProjection R I d w ≫ polynomialHilbertChartι R I d w :=
  pullback.lift_fst _ _ _

/-- The ambient chart retains its original polynomial-space projection. -/
@[reassoc]
theorem polynomialHilbertAmbientChart_snd :
    polynomialHilbertAmbientChart R I d w ≫ pullback.snd _ _ =
      chartPolynomialOriginal R I d w := pullback.lift_snd _ _ _

/-- The ambient chart is the actual inverse image of the corresponding parameter chart. -/
theorem polynomialHilbertAmbientChart_isPullback :
    IsPullback (polynomialHilbertAmbientChart R I d w) (chartPolynomialProjection R I d w)
      (pullback.fst _ _) (polynomialHilbertChartι R I d w) := by
  have h : IsPullback (chartPolynomialProjection R I d w)
      (polynomialHilbertAmbientChart R I d w ≫ pullback.snd _ _)
      (polynomialHilbertChartι R I d w ≫ polynomialHilbertStructure R I d)
      (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial I R)))) := by
    rw [polynomialHilbertAmbientChart_snd, polynomialHilbertChartι_over]
    exact chartPolynomial_isPullback R I d w
  exact (h.of_bot (polynomialHilbertAmbientChart_fst R I d w).symm
    (IsPullback.of_hasPullback _ _)).flip

/-- Each polynomial chart is an open subscheme of the actual ambient space. -/
instance polynomialHilbertAmbientChart_isOpenImmersion :
    IsOpenImmersion (polynomialHilbertAmbientChart R I d w) :=
  MorphismProperty.of_isPullback (polynomialHilbertAmbientChart_isPullback R I d w).flip
    (inferInstanceAs (IsOpenImmersion (polynomialHilbertChartι R I d w)))

end FLT.Mazur.HilbertChart
