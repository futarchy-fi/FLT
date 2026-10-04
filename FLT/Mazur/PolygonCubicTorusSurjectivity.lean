/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCubicTorusChart
public import FLT.Mazur.LaurentRingSurjectivity

/-!
# Surjectivity of the polygon cubic map on each torus chart

Actual interpolation-coordinate images generate constants, T, and T⁻¹. The
result is surjectivity of the existing projective chart ring map restricted
to each torus image, including the one-gon self-incidence correction.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
open scoped Polynomial LaurentPolynomial
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonCubicSections
open FCurve PolygonPinching PolygonPowerNodeEndpoints ProjectiveLineMarkedSectionTransition
attribute [local instance] MvPolynomial.gradedAlgebra
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Fin n → Kˣ)

/-- The actual projective chart ring map is onto the Laurent coordinates of each torus. -/
theorem torusChartRingMap_surjective (i : Fin n) :
    Function.Surjective (torusChartRingMap K n hn p q h a i) := by
  apply laurent_surjective_of_perturbed_inverse _
    (weight K n a 3 i * cubicDelta K n i 0 0 ((finRotate n).symm i))
  · intro c
    exact ⟨ProjectiveSpace.chartScalars K (Fin (n * 3 + 1 + 1)) (interiorIndex.{u} n) c,
      torusChartRingMap_scalar K n hn p q h a i c⟩
  · refine ⟨ProjectiveSpace.coordinate K (Fin (n * 3 + 1 + 1)) (interiorIndex.{u} n)
      ((cubicCoordinateEquiv n).symm (.inr ⟨(i, 2)⟩)), ?_⟩
    rw [torusChartRingMap_coordinate, torusRatio_quadratic, RingEquiv.symm_apply_apply]
  · refine ⟨ProjectiveSpace.coordinate K (Fin (n * 3 + 1 + 1)) (interiorIndex.{u} n)
      ((cubicCoordinateEquiv n).symm (.inr ⟨(i, 0)⟩)), ?_⟩
    rw [torusChartRingMap_coordinate, torusRatio_node, RingEquiv.symm_apply_apply]

/-- Surjectivity holds in the genuine structure-sheaf ring on the torus image. -/
theorem torus_sectionProjectiveChartRingMap_surjective (i : Fin n) :
    let := torus_isOpenImmersion K n hn p q h i
    Function.Surjective (sectionProjectiveChartRingMap (polygonLine K n hn p q h a 3)
      (n * 3 + 1) (finiteCubicFamily K n hn p q h a) (interiorIndex.{u} n)
      ((torusToComponent K ≫ componentι K n i ≫ p).left ''ᵁ ⊤)
      (torus_image_le_interior K n hn p q h a i) (cubicOpenScalars K _)) := by
  let := torus_isOpenImmersion K n hn p q h i
  dsimp only
  intro b
  obtain ⟨x, hx⟩ := torusChartRingMap_surjective K n hn p q h a i
    ((laurentRing K).symm (((torusToComponent K ≫ componentι K n i ≫ p).left.appIso ⊤).hom b))
  refine ⟨x, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso
    ((torusToComponent K ≫ componentι K n i ≫ p).left.appIso ⊤).hom).injective
  apply (laurentRing K).symm.injective
  rw [torusChartRingMap_apply] at hx
  exact hx

end FLT.Mazur.PolygonCubicSections
