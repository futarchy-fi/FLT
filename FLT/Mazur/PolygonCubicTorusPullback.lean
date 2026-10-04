/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCubicTorusSurjectivity
public import FLT.Mazur.PolygonCubicProjectiveMorphism
public import FLT.Mazur.ModuleSectionProjectiveTransition

/-!
# Actual structure-sheaf surjectivity on polygon torus opens

Identify the chart ring map with the pullback of regular functions along the
existing global cubic projective morphism, then transfer its proved surjectivity.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonCubicSections
open FCurve PolygonPinching PolygonPowerNodeEndpoints ProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Fin n → Kˣ)

/-- Each torus image maps into the interior standard projective chart. -/
lemma torus_image_le_projective_preimage (i : Fin n) :
    let := torus_isOpenImmersion K n hn p q h i
    (torusToComponent K ≫ componentι K n i ≫ p).left ''ᵁ ⊤ ≤
      cubicProjectiveMorphism K n hn p q h a ⁻¹ᵁ
        chart K (Fin (n * 3 + 1 + 1)) (interiorIndex.{0} n) := by
  let := torus_isOpenImmersion K n hn p q h i
  rw [cubicProjectiveMorphism_preimage_chart]
  simpa only [finiteCubicOpen, cubicOpen, finiteCubicFamily] using
    torus_image_le_interior K n hn p q h a i

/-- Pullback of every chart-ring section is the actual ring map already computed. -/
lemma torus_projective_chartSection (i : Fin n)
    (x : chartRing K (Fin (n * 3 + 1 + 1)) (interiorIndex.{0} n)) :
    let := torus_isOpenImmersion K n hn p q h i
    (cubicProjectiveMorphism K n hn p q h a).appLE
      (chart K (Fin (n * 3 + 1 + 1)) (interiorIndex.{0} n))
      ((torusToComponent K ≫ componentι K n i ≫ p).left ''ᵁ ⊤)
      (torus_image_le_projective_preimage K n hn p q h a i)
      (Proj.awayToSection (grading K (Fin (n * 3 + 1 + 1)))
        (MvPolynomial.X (interiorIndex.{0} n)) x) =
      sectionProjectiveChartRingMap (polygonLine K n hn p q h a 3) (n * 3 + 1)
        (finiteCubicFamily K n hn p q h a) (interiorIndex.{0} n) _
        (torus_image_le_interior K n hn p q h a i) (cubicOpenScalars K _) x := by
  let := torus_isOpenImmersion K n hn p q h i
  apply chartSection_evaluation_apply
  exact sectionProjectiveMorphism_onOpen (polygonLine K n hn p q h a 3) (n * 3 + 1)
    (finiteCubicFamily K n hn p q h a) (iSup_finiteCubicOpen K n hn p q h a)
    (C.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom) _ _
    (torus_image_le_interior K n hn p q h a i)

/-- The genuine structure-sheaf pullback to each torus image is surjective. -/
theorem torus_projective_appLE_surjective (i : Fin n) :
    let := torus_isOpenImmersion K n hn p q h i
    Function.Surjective ((cubicProjectiveMorphism K n hn p q h a).appLE
      (chart K (Fin (n * 3 + 1 + 1)) (interiorIndex.{0} n))
      ((torusToComponent K ≫ componentι K n i ≫ p).left ''ᵁ ⊤)
      (torus_image_le_projective_preimage K n hn p q h a i)) := by
  let := torus_isOpenImmersion K n hn p q h i
  dsimp only
  intro b
  obtain ⟨x, hx⟩ := torus_sectionProjectiveChartRingMap_surjective K n hn p q h a i b
  refine ⟨Proj.awayToSection (grading K (Fin (n * 3 + 1 + 1)))
    (MvPolynomial.X (interiorIndex.{0} n)) x, ?_⟩
  exact (torus_projective_chartSection K n hn p q h a i x).trans hx

end FLT.Mazur.PolygonCubicSections
