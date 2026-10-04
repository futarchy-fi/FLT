/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCubicTorusGenerator
public import FLT.Mazur.ProjectiveLineInteriorRatios

/-!
# Actual Laurent ratios of polygon cubic sections

The torus pullback of a polygon section divided by the uniform interior
section has Laurent coordinate P/T, where P is its interpolation polynomial.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
open scoped Polynomial LaurentPolynomial
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

/-- The compared interior section generates on the composite component torus chart. -/
lemma component_interior_isIso (i : Fin n) :
    IsIso (globalSectionHom _ (pullGlobal (torusToComponent K).left _
      (componentSection K n hn p q h a (nodeSection K n hn p q h a 0 1 0) i))) := by
  have := interiorSection_isIso K (a i) 3
    (componentSection K n hn p q h a (nodeSection K n hn p q h a 0 1 0) i)
    (interior_component_polynomial K n hn p q h a i)
  exact globalSectionHom_isIso_comp_pullGlobal
    (ProjectiveLine.overlapLeft K) (ProjectiveLine.left K) _ _

/-- The component comparison identifies the actual torus ratio with its Laurent formula. -/
lemma component_interior_ratio (i : Fin n)
    (s : Γ(polygonLine K n hn p q h a 3, ⊤)) :
    let := component_interior_isIso K n hn p q h a i
    sectionRatio _
      (pullGlobal (torusToComponent K).left _
        (componentSection K n hn p q h a (nodeSection K n hn p q h a 0 1 0) i))
      (pullGlobal (torusToComponent K).left _ (componentSection K n hn p q h a s i)) =
      laurentRing K (Polynomial.toLaurent
        (((sectionEquiv K n hn p q h a 2 s).val i).val) * LaurentPolynomial.T (-1)) := by
  have he := interiorSection_ratio_comp K (a i) 3
      (componentSection K n hn p q h a (nodeSection K n hn p q h a 0 1 0) i)
      (componentSection K n hn p q h a s i)
      (interior_component_polynomial K n hn p q h a i)
  rw [componentSection_polynomial] at he
  exact he

/-- The ratio on the genuine polygon torus chart is the interpolation polynomial over T. -/
lemma torus_interior_ratio (i : Fin n)
    (s : Γ(polygonLine K n hn p q h a 3, ⊤)) :
    let := interiorSection_isIso_torus K n hn p q h a i
    sectionRatio _
      (pullGlobal (torusToComponent K ≫ componentι K n i ≫ p).left _
        (nodeSection K n hn p q h a 0 1 0))
      (pullGlobal (torusToComponent K ≫ componentι K n i ≫ p).left _ s) =
      laurentRing K (Polynomial.toLaurent
        (((sectionEquiv K n hn p q h a 2 s).val i).val) * LaurentPolynomial.T (-1)) := by
  let := interiorSection_isIso_torus K n hn p q h a i
  let v := nodeSection K n hn p q h a 0 1 0
  have ht := interiorSection_isIso K (a i) 3
    (componentSection K n hn p q h a v i) (interior_component_polynomial K n hn p q h a i)
  have hc := globalSectionHom_isIso_comp_pullGlobal
    (ProjectiveLine.overlapLeft K) (ProjectiveLine.left K) _
    (componentSection K n hn p q h a v i)
  change IsIso (globalSectionHom _ (pullGlobal (torusToComponent K).left _
    (componentSection K n hn p q h a v i))) at hc
  dsimp only [componentSection] at hc
  have hb := globalSectionHom_isIso_pullback_transport (torusToComponent K).left
    (PolygonDirectPowerComparison.lineIso K n hn p q h a i 3)
    (pullGlobal (componentι K n i ≫ p).left _ v)
  change sectionRatio _
    (pullGlobal ((torusToComponent K).left ≫ (componentι K n i ≫ p).left) _ v)
    (pullGlobal ((torusToComponent K).left ≫ (componentι K n i ≫ p).left) _ s) = _
  rw [sectionRatio_comp_pullGlobal]
  exact (sectionRatio_pullGlobal_transport (torusToComponent K).left
    (PolygonDirectPowerComparison.lineIso K n hn p q h a i 3)
    (pullGlobal (componentι K n i ≫ p).left _ v)
    (pullGlobal (componentι K n i ≫ p).left _ s)).trans
      (component_interior_ratio K n hn p q h a i s)

end FLT.Mazur.PolygonCubicSections
