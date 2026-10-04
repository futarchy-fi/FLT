/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveLineSealedCanonicalRatios
public import FLT.Mazur.ProjectiveLineCanonicalRatios
public import FLT.Mazur.PolygonCubicComponentSection
public import FLT.Mazur.ProjectiveLineRightCanonicalRatios

/-!
# Canonical ratios of actual component sections

Compute the canonical ratios of the genuine compared component sections on
both punctured normalization charts. Weighted reversal relates the right
numerator to the polygon interpolation polynomial.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open scoped Polynomial
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonCubicSections
open FCurve PolygonPinching PolygonPowerNodeEndpoints ProjectiveLineMarkedHZero
open ProjectiveLineMarkedSectionTransition
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Fin n → Kˣ)

/-- The actual component ratio has its interpolation polynomial as numerator. -/
lemma sealed_component_canonical_ratio (i : Fin n)
    (s : Γ(polygonLine K n hn p q h a 3, ⊤)) :
    let := ProjectiveLineCanonicalRatios.toLine_canonical_isIso K (a i) 3
    pullbackSectionRatio (ProjectiveLineCanonicalRatios.toLine K (a i))
      (line K (a i) 3)
      (divisorSection ((ProjectiveLineMarkedCharts.relativeCartier K (a i)).1.pow 3) ⊤)
      (componentSection K n hn p q h a s i) =
      ProjectiveLineCanonicalRatios.coordinates K (a i)
        (algebraMap K[X] (ProjectiveLineCanonicalRatios.ring K (a i))
          (((sectionEquiv K n hn p q h a 2 s).val i).val) *
          IsLocalization.Away.invSelf (Polynomial.X - Polynomial.C (a i : K)) ^ 3) := by
  have he := ProjectiveLineCanonicalRatios.sealed_canonical_ratio K (a i) 3
    (componentSection K n hn p q h a s i)
  rw [componentSection_polynomial] at he
  exact he

/-- The actual right component ratio has its right polynomial numerator. -/
lemma sealed_right_component_canonical_ratio (i : Fin n)
    (s : Γ(polygonLine K n hn p q h a 3, ⊤)) :
    let := ProjectiveLineRightCanonicalRatios.toLine_canonical_isIso K (a i) 3
    pullbackSectionRatio (ProjectiveLineRightCanonicalRatios.toLine K (a i))
      (line K (a i) 3)
      (divisorSection ((ProjectiveLineMarkedCharts.relativeCartier K (a i)).1.pow 3) ⊤)
      (componentSection K n hn p q h a s i) =
      ProjectiveLineCanonicalRatios.coordinates K (a i)⁻¹
        (algebraMap K[X] (ProjectiveLineCanonicalRatios.ring K (a i)⁻¹)
          (ProjectiveLineRightCanonicalRatios.sectionPolynomial K (a i) 3
            (componentSection K n hn p q h a s i)) *
          IsLocalization.Away.invSelf (Polynomial.X - Polynomial.C (↑(a i)⁻¹ : K)) ^ 3) :=
  ProjectiveLineRightCanonicalRatios.sealed_canonical_ratio K (a i) 3
    (componentSection K n hn p q h a s i)

/-- The right component coefficients are weighted reversals of interpolation coefficients. -/
lemma right_component_canonical_coeff (i : Fin n)
    (s : Γ(polygonLine K n hn p q h a 3, ⊤)) (j : ℕ) (hj : j ≤ 3) :
    (ProjectiveLineRightCanonicalRatios.sectionPolynomial K (a i) 3
      (componentSection K n hn p q h a s i)).coeff j =
      (↑((-(a i))⁻¹) : K) ^ 3 *
        (((sectionEquiv K n hn p q h a 2 s).val i).val).coeff (3 - j) := by
  rw [ProjectiveLineRightCanonicalRatios.sectionPolynomial_coeff K (a i) 3 _ j hj,
    componentSection_polynomial]

end FLT.Mazur.PolygonCubicSections
