/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleGlobalSectionExt
public import FLT.Mazur.ProjectiveLineMarkedPolynomialBounds
/-!
# Injectivity of marked divisor polynomial coordinates

Every genuine global section is determined by its bounded left polynomial.
The Laurent transition determines the right polynomial, and the two affine
charts detect equality. Surjectivity requires a separate sheaf gluing proof.
-/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open scoped Polynomial LaurentPolynomial
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.ProjectiveLineMarkedSectionInjective
open FCurve ProjectiveLineMarkedSectionTransition ProjectiveLineMarkedPullbackCoordinates
open ProjectiveLineMarkedDualCoordinates ProjectiveLineMarkedCharts
open PolygonDivisorNormalizationPullback
variable (K : Type u) [Field K]
/-- Equal polynomial coordinates give equal actual pulled-back sections. -/
lemma chart_section_eq (a : Kˣ) (m : ℕ)
    (j : ProjectiveLine.chart K ⟶ ProjectiveLine.scheme K) [IsOpenImmersion j]
    (b : K) (hj : (markedPoint K a).ker.comap j = (chartPoint K b).ker)
    (s t : structureModule (ProjectiveLine.scheme K) ⟶ line K a m)
    (h : polynomial K a m j b hj s = polynomial K a m j b hj t) :
    pullGlobal j (line K a m) (s.app ⊤ (1 : Γ(ProjectiveLine.scheme K, ⊤))) =
      pullGlobal j (line K a m) (t.app ⊤ (1 : Γ(ProjectiveLine.scheme K, ⊤))) := by
  apply (chartSectionsCoordinate K a j b hj m).injective
  rw [← polynomial_coordinate, ← polynomial_coordinate, h]
/-- The left polynomial determines an actual global section uniquely. -/
lemma leftPolynomial_injective (a : Kˣ) (m : ℕ) :
    Function.Injective (leftPolynomial K a m) := by
  intro s t h
  have hr : rightPolynomial K a m s = rightPolynomial K a m t := by
    apply Polynomial.toLaurent_injective
    apply LaurentPolynomial.invert.injective
    rw [transition, transition, h]
  apply globalSection_hom_ext
  apply pullGlobal_openCover_ext (ProjectiveLineProductCharts.chartCover K) (line K a m)
  intro b
  cases b
  · exact chart_section_eq K a m _ _ (left_ideal K a) s t h
  · exact chart_section_eq K a m _ _ (right_ideal K a) s t hr

/-- The bounded polynomial associated to an actual marked divisor section. -/
def boundedPolynomial (a : Kˣ) (m : ℕ)
    (s : structureModule (ProjectiveLine.scheme K) ⟶ line K a m) :
    Polynomial.degreeLT K (m + 1) :=
  ⟨leftPolynomial K a m s,
    ProjectiveLineMarkedPolynomialBounds.leftPolynomial_bounded K a m s⟩
/-- The actual global-section map to bounded polynomials is injective. -/
lemma boundedPolynomial_injective (a : Kˣ) (m : ℕ) :
    Function.Injective (boundedPolynomial K a m) := by
  intro s t h
  exact leftPolynomial_injective K a m (congrArg Subtype.val h)
end FLT.Mazur.ProjectiveLineMarkedSectionInjective
