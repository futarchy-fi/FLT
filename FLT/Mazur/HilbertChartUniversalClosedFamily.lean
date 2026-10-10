/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertChartUniversalFamily
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# The universal closed family in the actual affine base change

The ambient tensor-product spectrum is proved to be a pullback. Surjective
evaluation realizes the finite locally free chart family as its closed subscheme.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace FLT.Mazur.HilbertChart

universe u

variable (R : Type u) [CommRing R] (I : Type u) (d : ℕ)
variable (w : Fin d → MvPolynomial I R)

/-- Cache the coefficient-ring instance for nested tensor inference. -/
local instance closedFamilyCoefficientsRing : CommRing (Coefficients R I d) := inferInstance

/-- Cache the chart-ring instance for nested tensor inference. -/
local instance closedFamilyChartRing : CommRing (ChartRing R I d w) := inferInstance

/-- The coordinate ring of the actual ambient affine base change. -/
abbrev AmbientRing := ChartRing R I d w ⊗[R] MvPolynomial I R

/-- The actual ambient base-change scheme. -/
abbrev chartAmbient : Scheme := Spec (CommRingCat.of (AmbientRing R I d w))

/-- Projection of the ambient base change to the parameter chart. -/
def chartAmbientToChart : chartAmbient R I d w ⟶ chartScheme R I d w :=
  Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom)

/-- Projection of the ambient base change to the original affine space. -/
def chartAmbientToOriginal : chartAmbient R I d w ⟶ Spec (CommRingCat.of (MvPolynomial I R)) :=
  Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom)

/-- The ambient tensor spectrum satisfies the actual scheme pullback property. -/
theorem chartAmbient_isPullback :
    IsPullback (chartAmbientToChart R I d w) (chartAmbientToOriginal R I d w)
      (Spec.map (CommRingCat.ofHom (algebraMap R (ChartRing R I d w))))
      (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial I R)))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct R (ChartRing R I d w) (MvPolynomial I R))

/-- The polynomial tensor equivalence followed by actual evaluation. -/
def ambientEvaluation : AmbientRing R I d w →ₐ[ChartRing R I d w] ChartAlgebra R I d w :=
  (chartEvaluation R I d w).comp
    (MvPolynomial.algebraTensorAlgEquiv R (ChartRing R I d w)).toAlgHom

/-- The ambient tensor evaluation is surjective. -/
theorem ambientEvaluation_surjective : Function.Surjective (ambientEvaluation R I d w) :=
  (chartEvaluation_surjective R I d w).comp
    (MvPolynomial.algebraTensorAlgEquiv R (ChartRing R I d w)).surjective

/-- The actual closed immersion of the universal chart family into the ambient base change. -/
def chartClosedImmersion : chartFamily R I d w ⟶ chartAmbient R I d w :=
  Spec.map (CommRingCat.ofHom (ambientEvaluation R I d w).toRingHom)

instance : IsClosedImmersion (chartClosedImmersion R I d w) :=
  IsClosedImmersion.spec_of_surjective _ (ambientEvaluation_surjective R I d w)

/-- The closed immersion is over the actual parameter chart. -/
theorem chartClosedImmersion_over :
    chartClosedImmersion R I d w ≫ chartAmbientToChart R I d w = chartFamilyMap R I d w := by
  rw [chartClosedImmersion, chartAmbientToChart, ← Spec.map_comp, chartFamilyMap]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (ambientEvaluation R I d w).commutes r

end FLT.Mazur.HilbertChart
