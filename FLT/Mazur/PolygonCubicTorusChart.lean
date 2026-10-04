/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCubicTorusImages
public import FLT.Mazur.ModuleSectionRatioOpenPullback
public import FLT.Mazur.TorusChartScalars

/-!
# Laurent coordinates of the actual polygon projective chart map

Restrict the existing projective chart ring map to the image of a torus chart,
then use its actual open-immersion section isomorphism and Laurent coordinates.
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

/-- The finite projective index of the uniform interior section. -/
def interiorIndex (n : ℕ) : Fin (n * 3 + 1 + 1) :=
  (cubicCoordinateEquiv.{u} n).symm (.inl ⟨true⟩)

variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Fin n → Kˣ)

/-- The chosen projective denominator is exactly the uniform interior section. -/
lemma finiteCubicFamily_interiorIndex :
    finiteCubicFamily K n hn p q h a (interiorIndex.{u} n) =
      nodeSection K n hn p q h a 0 1 0 := by
  simp only [finiteCubicFamily, interiorIndex, Equiv.apply_symm_apply, cubicFamily,
    generatingPair]

/-- Every torus image lies in the genuine interior denominator open. -/
lemma torus_image_le_interior (i : Fin n) :
    let := torus_isOpenImmersion K n hn p q h i
    (torusToComponent K ≫ componentι K n i ≫ p).left ''ᵁ ⊤ ≤
      sectionGeneratorOpen (polygonLine K n hn p q h a 3)
        (finiteCubicFamily K n hn p q h a (interiorIndex.{u} n)) := by
  let := torus_isOpenImmersion K n hn p q h i
  dsimp only
  rw [finiteCubicFamily_interiorIndex, Scheme.Hom.image_top_eq_opensRange]
  have := interiorSection_isIso_torusOpen K n hn p q h a i
  exact le_sectionGeneratorOpen _ _ (torusOpen K n hn p q h i)

/-- The existing projective chart ring map in canonical coordinates on a torus. -/
irreducible_def torusChartRingMap (i : Fin n) :
    ProjectiveSpace.chartRing K (Fin (n * 3 + 1 + 1)) (interiorIndex.{u} n) →+* K[T;T⁻¹] :=
  let := torus_isOpenImmersion K n hn p q h i
  (laurentRing K).symm.toRingHom.comp
    (((torusToComponent K ≫ componentι K n i ≫ p).left.appIso ⊤).hom.hom.comp
      (sectionProjectiveChartRingMap (polygonLine K n hn p q h a 3) (n * 3 + 1)
        (finiteCubicFamily K n hn p q h a) (interiorIndex.{u} n) _
        (torus_image_le_interior K n hn p q h a i) (cubicOpenScalars K _)))

/-- Evaluation of the sealed chart map retains the two actual section comparisons. -/
lemma torusChartRingMap_apply (i : Fin n)
    (x : ProjectiveSpace.chartRing K (Fin (n * 3 + 1 + 1)) (interiorIndex.{u} n)) :
    let := torus_isOpenImmersion K n hn p q h i
    torusChartRingMap K n hn p q h a i x = (laurentRing K).symm
      (((torusToComponent K ≫ componentι K n i ≫ p).left.appIso ⊤).hom
        (sectionProjectiveChartRingMap (polygonLine K n hn p q h a 3) (n * 3 + 1)
          (finiteCubicFamily K n hn p q h a) (interiorIndex.{u} n) _
          (torus_image_le_interior K n hn p q h a i) (cubicOpenScalars K _) x)) := by
  rw [torusChartRingMap_def]
  rfl

/-- Every actual chart coordinate restricts to its interpolation Laurent expression. -/
lemma torusChartRingMap_coordinate (i : Fin n) (j : CubicIndex.{u} n) :
    torusChartRingMap K n hn p q h a i
      (ProjectiveSpace.coordinate K (Fin (n * 3 + 1 + 1)) (interiorIndex.{u} n)
        ((cubicCoordinateEquiv n).symm j)) =
      (laurentRing K).symm (torusRatio K n hn p q h a i (cubicFamily K n hn p q h a j)) := by
  let := torus_isOpenImmersion K n hn p q h i
  let := interiorSection_isIso_torus K n hn p q h a i
  rw [torusChartRingMap_apply,
    sectionProjectiveChartRingMap_coordinate]
  apply congrArg (laurentRing K).symm
  have hf := torus_image_le_interior K n hn p q h a i
  rw [finiteCubicFamily_interiorIndex] at hf
  simp only [finiteCubicFamily, interiorIndex, Equiv.apply_symm_apply,
    cubicFamily_inl, generatingPair]
  rw [torusRatio_def]
  exact sectionRatioOn_openPullback _ _ _ _ hf

/-- The actual coefficient map becomes the Laurent constant map. -/
lemma torusChartRingMap_scalar (i : Fin n) (c : K) :
    torusChartRingMap K n hn p q h a i
      (ProjectiveSpace.chartScalars K (Fin (n * 3 + 1 + 1)) (interiorIndex.{u} n) c) =
      LaurentPolynomial.C c := by
  let := torus_isOpenImmersion K n hn p q h i
  rw [torusChartRingMap_apply,
    sectionProjectiveChartRingMap_scalar, torus_image_scalar, RingEquiv.symm_apply_apply]

end FLT.Mazur.PolygonCubicSections
