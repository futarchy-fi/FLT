/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIntegralCoefficientMap
public import FLT.Mazur.WeierstrassIntegralProjectivePreimage

/-!
# Chart inverse images under coefficient extension

A normalized chart is selected by the same coordinate nonvanishing before and
after coefficient extension. Hence each source chart is exactly the inverse
image of its original chart under the global coefficient morphism.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra

universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R)

/-- Intersecting two normalized charts imposes precisely one coordinate nonvanishing. -/
theorem integralCurveChart_preimage_chart (j k : Fin 3) :
    integralCurveChart W j ⁻¹ᵁ (integralCurveChart W k).opensRange =
      PrimeSpectrum.basicOpen (coord W j k) := by
  rw [← integralProjectiveMap_preimage_chart, ← Scheme.Hom.comp_preimage,
    integralCurveChart_projectiveMap]
  ext x
  exact projectiveChartMap_mem_iff W j k x

/-- The global coefficient map pulls each original chart back to the corresponding new chart. -/
theorem integralCoefficientMorphism_preimage_chart (j : Fin 3) :
    integralCoefficientMorphism (S := S) W ⁻¹ᵁ (integralCurveChart W j).opensRange =
      (integralCurveChart (W.map (algebraMap R S)) j).opensRange := by
  have h (k : Fin 3) :
      integralCurveChart (W.map (algebraMap R S)) k ⁻¹ᵁ
          (integralCoefficientMorphism W ⁻¹ᵁ (integralCurveChart W j).opensRange) =
        integralCurveChart (W.map (algebraMap R S)) k ⁻¹ᵁ
          (integralCurveChart (W.map (algebraMap R S)) j).opensRange := by
    rw [← Scheme.Hom.comp_preimage, integralCurveChart_coefficientMorphism,
      Scheme.Hom.comp_preimage, integralCurveChart_preimage_chart,
      integralCurveChart_preimage_chart]
    change Spec.map (CommRingCat.ofHom (chartCoefficientMap W k).toRingHom) ⁻¹ᵁ
      PrimeSpectrum.basicOpen (coord W k j) = _
    rw [SpecMap_preimage_basicOpen]
    exact congrArg PrimeSpectrum.basicOpen (chartCoefficientMap_coord W k j)
  ext x
  obtain ⟨k, y, rfl⟩ := integralCurveChart_cover (W.map (algebraMap R S)) x
  exact iff_of_eq (congrArg (fun U => y ∈ U) (h k))

/-- The affine coefficient chart square is the pullback along the original chart inclusion. -/
theorem integralCoefficientChart_isPullback (j : Fin 3) :
    IsPullback (integralCurveChart (W.map (algebraMap R S)) j)
      (chartCoefficientMorphism W j) (integralCoefficientMorphism W) (integralCurveChart W j) := by
  apply IsPullback.flip
  apply IsOpenImmersion.isPullback
  · exact integralCurveChart_coefficientMorphism W j
  · exact integralCoefficientMorphism_preimage_chart W j

end FLT.Mazur.WeierstrassIntegralChart
