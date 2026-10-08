/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCubicQuotient
public import FLT.Mazur.WeierstrassCubicSection
public import FLT.Mazur.ProjectiveChartSectionPullback

/-!
# The cubic quotient on its original charts

The ambient quotient followed by restriction to an original cubic chart is
exactly the specified chart algebra. Since that chart is the entire inverse
image, this computes the genuine quotient's kernel as the principal cubic ideal.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial
open FLT.Mazur.ProjectiveSpace FLT.Mazur.FCurve

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type} [CommRing R] (W : WeierstrassCurve R) (j : Fin 3)

/-- The original chart lies entirely over the matching ambient standard open. -/
theorem cubicChart_preimage_top :
    (integralCurveChart W j) ⁻¹ᵁ (integralProjectiveMap W ⁻¹ᵁ chart R (Fin 3) j) = ⊤ := by
  rw [integralProjectiveMap_preimage_chart]
  simp

/-- Pull sections on the entire inverse image back to its original affine chart. -/
def cubicChartSections :
    Γ(integralCurve W, integralProjectiveMap W ⁻¹ᵁ chart R (Fin 3) j) ⟶
      Γ(chartScheme W j, ⊤) :=
  (integralCurveChart W j).appLE _ ⊤ (cubicChart_preimage_top W j).ge

/-- This chart pullback is an isomorphism, since the chart exhausts the inverse image. -/
instance cubicChartSections_isIso : IsIso (cubicChartSections W j) := by
  unfold cubicChartSections
  generalize_proofs h
  have he : integralProjectiveMap W ⁻¹ᵁ chart R (Fin 3) j =
      integralCurveChart W j ''ᵁ ⊤ := by
    rw [integralProjectiveMap_preimage_chart, Scheme.Hom.image_top_eq_opensRange]
  have : IsIso ((integralCurveChart W j).appLE _ ⊤ h ≫
      ((integralCurveChart W j).appIso ⊤).inv) := by
    rw [Scheme.Hom.appLE_appIso_inv]
    exact inferInstanceAs
      (IsIso ((integralCurve W).presheaf.map (eqToHom he.symm).op))
  exact IsIso.of_isIso_comp_right _ ((integralCurveChart W j).appIso ⊤).inv

/-- The actual ring pullback agrees with the original ambient chart quotient. -/
theorem cubicQuotient_chart_comparison :
    Proj.awayToSection (grading R (Fin 3)) (X j) ≫
        (integralProjectiveMap W).app (chart R (Fin 3) j) ≫ cubicChartSections W j =
      CommRingCat.ofHom (projectiveChartAlgebra W j).toRingHom ≫
        (Scheme.ΓSpecIso (.of (Coordinate W j))).inv := by
  have hc := Scheme.Hom.appLE_comp_appLE (integralCurveChart W j)
    (integralProjectiveMap W) (chart R (Fin 3) j)
    (integralProjectiveMap W ⁻¹ᵁ chart R (Fin 3) j) ⊤ le_rfl
    (cubicChart_preimage_top W j).ge
  rw [← Scheme.Hom.app_eq_appLE] at hc
  simp only [integralCurveChart_projectiveMap] at hc
  change _ ≫ (integralProjectiveMap W).app _ ≫ cubicChartSections W j = _
  dsimp only [cubicChartSections]
  erw [hc]
  have hp := Scheme.Hom.appLE_comp_appLE (projectiveChartMorphism W j)
    (chartMap R (Fin 3) j) (chart R (Fin 3) j) ⊤ ⊤
    (chartMap_chart_preimage_top R (Fin 3) j).ge (by simp)
  change _ = (projectiveChartMap W j).appLE _ _ _ at hp
  rw [← hp, ← Category.assoc, chartSection_chartMap]
  change (Scheme.ΓSpecIso _).inv ≫ (Spec.map _).appTop = _
  exact (Scheme.ΓSpecIso_inv_naturality _).symm

/-- Vanishing in the genuine quotient is detected by the original chart algebra. -/
theorem cubicQuotient_chart_zero_iff (a : chartRing R (Fin 3) j) :
    (integralProjectiveMap W).app (chart R (Fin 3) j)
        (Proj.awayToSection (grading R (Fin 3)) (X j) a) = 0 ↔
      projectiveChartAlgebra W j a = 0 := by
  have h := ConcreteCategory.congr_hom (cubicQuotient_chart_comparison W j) a
  change cubicChartSections W j ((integralProjectiveMap W).app _
    (Proj.awayToSection _ _ a)) = (Scheme.ΓSpecIso _).inv (projectiveChartAlgebra W j a) at h
  rw [← map_eq_zero_iff (cubicChartSections W j).hom
    (ConcreteCategory.bijective_of_isIso _).injective, h]
  exact map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso _).injective

/-- The original cubic coefficient vanishes under the structure-sheaf quotient. -/
theorem cubicEquationSection_quotient_zero :
    (integralProjectiveMap W).app (chart R (Fin 3) j) (cubicEquationSection W j) = 0 :=
  (cubicQuotient_chart_zero_iff W j _).mpr (projectiveChartAlgebra_equation W j)

/-- A chart function vanishes on the cubic precisely when its coefficient is in the cubic ideal. -/
theorem cubicQuotient_chart_mem_iff (a : chartRing R (Fin 3) j) :
    (integralProjectiveMap W).app (chart R (Fin 3) j)
        (Proj.awayToSection (grading R (Fin 3)) (X j) a) = 0 ↔
      a ∈ projectiveChartIdeal W j := by
  rw [cubicQuotient_chart_zero_iff, ← projectiveChartAlgebra_ker]
  rfl

end FLT.Mazur.WeierstrassIntegralChart
