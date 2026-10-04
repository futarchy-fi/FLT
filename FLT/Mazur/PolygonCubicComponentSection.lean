/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCubicChartGeneration
public import FLT.Mazur.ProjectiveLineInteriorGenerator

/-!
# Actual component sections of the polygon cubic

The sealed normalization restriction of a polygon section equals its direct
component pullback. This identifies the interpolation polynomial with the
left coordinate of the actual component section.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.LinePullbackRestriction
open FCurve
/-- Sealed restriction of a pulled-back global section is its direct pullback. -/
lemma sealedAlong_pullGlobal {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (p : Y ⟶ Z) (q : X ⟶ Z) (w : f ≫ p = q)
    (M : Z.Modules) (s : Γ(M, ⊤)) :
    (sealedAlong f p q w M).app ⊤ (pullGlobal p M s) = pullGlobal q M s := by
  subst q
  rw [sealedAlong_def, along]
  simp only [eqToHom_refl, Category.comp_id, restriction_appTop]
  exact pullGlobal_comp_hom f p M s
end FLT.Mazur.LinePullbackRestriction
namespace FLT.Mazur.PolygonCubicSections
open FCurve PolygonPinching PolygonPowerNodeEndpoints PolygonPowerBranchValues
open ProjectiveLineMarkedHZero LinePullbackRestriction
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Fin n → Kˣ)

/-- Pull a cubic section to its component through the existing divisor comparison. -/
def componentSection (s : Γ(polygonLine K n hn p q h a 3, ⊤)) (i : Fin n) :
    Γ(ProjectiveLineMarkedSectionTransition.line K (a i) 3, ⊤) :=
  (PolygonDirectPowerComparison.lineIso K n hn p q h a i 3).hom.app ⊤
    (pullGlobal (componentι K n i ≫ p).left _ s)

/-- The polynomial interpolation coordinate is the actual component-section coordinate. -/
lemma componentSection_polynomial (s : Γ(polygonLine K n hn p q h a 3, ⊤)) (i : Fin n) :
    sectionPolynomial K (a i) 3 (componentSection K n hn p q h a s i) =
      ((sectionEquiv K n hn p q h a 2 s).val i).val := by
  rw [sectionEquiv_val]
  change _ = (bounded K (a i) 3
    (componentClass K n hn p q h a 3 (pullGlobal p.left _ s) i)).val
  rw [bounded_val]
  simp only [componentClass, LinearEquiv.apply_symm_apply, sealedAlong_pullGlobal,
    componentSection]

/-- The uniform interior polygon section has actual component polynomial X. -/
lemma interior_component_polynomial (i : Fin n) :
    sectionPolynomial K (a i) 3 (componentSection K n hn p q h a
      (nodeSection K n hn p q h a 0 1 0) i) = Polynomial.X := by
  rw [componentSection_polynomial, interiorSection_polynomial]

end FLT.Mazur.PolygonCubicSections
