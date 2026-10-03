/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveLineFieldExtension
public import FLT.Mazur.ProjectiveLineUniversalAction

/-!
# Universal scaling and field extension

The coefficient maps on the actual projective line and Laurent parameter
commute with universal scaling. The proof compares the two polynomial
charts of the actual action product, retaining both projection equations.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped LaurentPolynomial Polynomial
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace FLT.Mazur.ProjectiveActionFieldExtension
open ProjectiveLineProductCharts ProjectiveLineUniversalAction
variable (K L : Type u) [Field K] [Field L] [Algebra K L]

/-- The projective-line map changing the coefficient field. -/
def coeff : ProjectiveLine.scheme L ⟶ ProjectiveLine.scheme K :=
  (ProjectiveLineFieldExtension.equivalence K L).inv ≫ pullback.snd _ _

@[reassoc] theorem chart_coeff (b : Bool) :
    (chartCover L).f b ≫ coeff K L =
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap K L))) ≫
        (chartCover K).f b := by
  cases b <;> simp [coeff, chartCover, ProjectiveLineFieldExtension.left_inv_assoc,
    ProjectiveLineFieldExtension.right_inv_assoc]

@[reassoc] theorem coeff_base : coeff K L ≫ ProjectiveLine.toBase K =
    ProjectiveLine.toBase L ≫ parameterToBase K L := by
  rw [coeff, Category.assoc, ← pullback.condition, ← Category.assoc,
    ProjectiveLineFieldExtension.inv_base]

/-- The Laurent coefficient map on multiplicative parameters. -/
def gmCoeff : (MultiplicativeGroupScheme.gm L).left ⟶ (MultiplicativeGroupScheme.gm K).left :=
  ProjectiveLineProductOverlap.coeff K L

@[reassoc] theorem gmCoeff_base : gmCoeff K L ≫ (MultiplicativeGroupScheme.gm K).hom =
    (MultiplicativeGroupScheme.gm L).hom ≫ parameterToBase K L := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext r
  simp

/-- Change both parameter and projective-line coordinates. -/
def productCoeff : product L (parameter L) ⟶ product K (parameter K) :=
  pullback.map _ _ _ _ (gmCoeff K L) (coeff K L) (parameterToBase K L)
    (gmCoeff_base K L).symm (coeff_base K L).symm

@[reassoc] theorem chart_productCoeff (b : Bool) :
    productChartMap L (parameter L) b ≫ productCoeff K L =
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
        (PolygonScalingNaturality.coeffMap (algebraMap K L)))) ≫
          productChartMap K (parameter K) b := by
  apply pullback.hom_ext
  · simp only [Category.assoc, productCoeff, pullback.map, pullback.lift_fst,
      productChartMap_fst_assoc, productChartMap_fst]
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    change Polynomial.C (PolygonScalingNaturality.coeffMap (algebraMap K L) r) =
      Polynomial.map (PolygonScalingNaturality.coeffMap (algebraMap K L)) (Polynomial.C r)
    simp
  · simp only [Category.assoc, productCoeff, pullback.map, pullback.lift_snd,
      productChartMap_snd_assoc, productChartMap_snd, chart_coeff]
    simp only [← Category.assoc, ← Spec.map_comp]
    congr 1
    congr 1
    ext <;> simp

/-- Universal scaling commutes with extension of the coefficient field. -/
theorem action_natural : productCoeff K L ≫ action K = action L ≫ coeff K L := by
  apply (productChartCover L (parameter L)).hom_ext
  intro b
  change productChartMap L (parameter L) b ≫ _ = productChartMap L (parameter L) b ≫ _
  rw [← Category.assoc, chart_productCoeff, Category.assoc]
  cases b
  · rw [left_action, left_action_assoc]
    have hc := chart_coeff K L false
    change ProjectiveLine.left L ≫ coeff K L = _ at hc
    rw [hc, ← Category.assoc, ← Category.assoc]
    congr 1
    simp only [leftMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
    apply CommRingCat.hom_ext
    ext <;> simp [PolygonUniversalScaling.scaleLeft, PolygonUniversalScaling.u,
      PolygonChartScaling.coordinateUnit]
  · rw [right_action, right_action_assoc]
    have hc := chart_coeff K L true
    change ProjectiveLine.right L ≫ coeff K L = _ at hc
    rw [hc, ← Category.assoc, ← Category.assoc]
    congr 1
    simp only [rightMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
    apply CommRingCat.hom_ext
    ext <;> simp [PolygonUniversalScaling.scaleRight, PolygonUniversalScaling.u,
      PolygonChartScaling.coordinateUnit]
end FLT.Mazur.ProjectiveActionFieldExtension
