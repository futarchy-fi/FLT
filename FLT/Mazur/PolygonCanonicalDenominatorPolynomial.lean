/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCanonicalTorusTransition
public import FLT.Mazur.SealedLineRestrictionSections

/-!
# The canonical denominator polynomial on each normalization component

The canonical section is preserved by the direct divisor-power comparison.
Its polynomial is the cube of the marked linear equation.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open scoped Polynomial LaurentPolynomial
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonCubicSections
open FCurve PolygonPinching PolygonPowerNodeEndpoints PolygonPowerBranchValues
open ProjectiveLineMarkedHZero ProjectiveLineMarkedSectionTransition LinePullbackRestriction
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Fin n → Kˣ)

/-- The polynomial of the actual canonical cubic section on component i. -/
lemma canonical_denominator_polynomial (i : Fin n) :
    ((sectionEquiv K n hn p q h a 2
      (finiteCubicFamily K n hn p q h a (canonicalIndex.{u} n))).val i).val =
      (Polynomial.X - Polynomial.C (a i : K)) ^ 3 := by
  rw [finiteCubicFamily_canonicalIndex, sectionEquiv_val]
  change (bounded K (a i) 3 (componentClass K n hn p q h a 3 _ i)).val = _
  rw [bounded_val, componentClass, LinearEquiv.apply_symm_apply]
  have hr (s : Γ(polygonLine K n hn p q h a 3, ⊤)) :
      (sealedAlong (componentι K n i).left p.left (componentι K n i ≫ p).left rfl
        (polygonLine K n hn p q h a 3)).app ⊤ (pullGlobal p.left _ s) =
      pullGlobal (componentι K n i ≫ p).left _ s := by
    rw [sealedAlong_def, along]
    simp only [eqToHom_refl, Category.comp_id]
    erw [restriction_appTop, pullGlobal_comp_hom]
    rfl
  rw [hr, PolygonDirectPowerComparison.lineIso_section, sectionPolynomial,
    coordinate_canonical]
  simp [ProjectiveLineMarkedDualCoordinates.equation]

/-- The actual torus chart sends the canonical denominator to its explicit Laurent expression. -/
lemma torusChartRingMap_canonical (i : Fin n) :
    torusChartRingMap K n hn p q h a i
      (ProjectiveSpace.coordinate K (Fin (n * 3 + 1 + 1)) (interiorIndex.{u} n)
        (canonicalIndex.{u} n)) =
      (LaurentPolynomial.T 1 - LaurentPolynomial.C (a i : K)) ^ 3 *
        LaurentPolynomial.T (-1) := by
  have hp := canonical_denominator_polynomial K n hn p q h a i
  simp only [finiteCubicFamily, canonicalIndex, Equiv.apply_symm_apply] at hp
  rw [canonicalIndex, torusChartRingMap_coordinate, torusRatio_eq,
    RingEquiv.symm_apply_apply, hp, map_pow, map_sub, Polynomial.toLaurent_X,
    Polynomial.toLaurent_C]

end FLT.Mazur.PolygonCubicSections
