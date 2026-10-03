/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleBinarySectionGluing
public import FLT.Mazur.ProjectiveLineChartIntersection
public import FLT.Mazur.ProjectiveLineMarkedSectionOverlap
public import FLT.Mazur.ProjectiveLineMarkedSectionInjective
/-!
# Global sections from bounded marked polynomials

The independent chart sections glue on the actual projective line. Every
bounded polynomial therefore comes from a genuine morphism out of the
structure module, proving surjectivity of the existing coordinate map.
-/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open scoped Polynomial LaurentPolynomial
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.ProjectiveLineMarkedSectionGluing
open FCurve ProjectiveLineMarkedSectionTransition ProjectiveLineMarkedSectionOverlap
open ProjectiveLineMarkedPullbackCoordinates ProjectiveLineMarkedDualCoordinates
open ProjectiveLineMarkedCharts ProjectiveLineMarkedPolynomialReciprocal
open ProjectiveLineMarkedSectionInjective
variable (K : Type u) [Field K] (a : Kˣ) (m : ℕ)
/-- A bounded polynomial and its reciprocal glue to a genuine global section. -/
lemma exists_section (p : Polynomial.degreeLT K (m + 1)) :
    ∃ s : Γ(line K a m, ⊤),
      pullGlobal (ProjectiveLine.left K) (line K a m) s = leftSection K a m p.val ∧
      pullGlobal (ProjectiveLine.right K) (line K a m) s =
        rightSection K a m (reciprocal a m p.val) :=
  pullOverlap_exists_glue (ProjectiveLine.overlapLeft K) (ProjectiveLine.left K)
    (ProjectiveLine.overlapRight K) (ProjectiveLine.right K)
    (ProjectiveLine.overlap_condition K) (line K a m)
    (leftSection K a m p.val) (rightSection K a m (reciprocal a m p.val))
    (bounded_overlap K a m p) (ProjectiveLine.overlap_image K).ge
    (ProjectiveLine.chart_images_cover K)
/-- Every bounded polynomial is the coordinate of an actual global-section morphism. -/
lemma boundedPolynomial_surjective : Function.Surjective (boundedPolynomial K a m) := by
  intro p
  obtain ⟨s, hs, _⟩ := exists_section K a m p
  refine ⟨globalSectionHom (line K a m) s, Subtype.ext ?_⟩
  change leftPolynomial K a m (globalSectionHom (line K a m) s) = p.val
  apply (coordinateRing K).injective
  unfold leftPolynomial
  rw [polynomial_coordinate, globalSectionHom_top, hs, leftSection,
    LinearEquiv.apply_symm_apply]
/-- The existing bounded-polynomial map is a bijection on actual section morphisms. -/
lemma boundedPolynomial_bijective : Function.Bijective (boundedPolynomial K a m) :=
  ⟨boundedPolynomial_injective K a m, boundedPolynomial_surjective K a m⟩
end FLT.Mazur.ProjectiveLineMarkedSectionGluing
