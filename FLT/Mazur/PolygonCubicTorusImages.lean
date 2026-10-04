/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCubicTorusRatios
public import FLT.Mazur.PolygonCubicFiniteFamily

/-!
# Interpolation-coordinate images on the polygon torus

The branch-quadratic coordinate gives T. The node-value coordinate gives
T⁻¹ plus a weighted T² term precisely when the component meets itself.
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
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Fin n → Kˣ)

/-- The ratio of an actual polygon section on the specified torus chart. -/
irreducible_def torusRatio (i : Fin n) (s : Γ(polygonLine K n hn p q h a 3, ⊤)) :
    Γ(ProjectiveLine.overlap K, ⊤) :=
  let := interiorSection_isIso_torus K n hn p q h a i
  sectionRatio _
    (pullGlobal (torusToComponent K ≫ componentι K n i ≫ p).left _
      (nodeSection K n hn p q h a 0 1 0))
    (pullGlobal (torusToComponent K ≫ componentι K n i ≫ p).left _ s)

/-- The sealed actual ratio has the previously proved Laurent expression. -/
lemma torusRatio_eq (i : Fin n) (s : Γ(polygonLine K n hn p q h a 3, ⊤)) :
    torusRatio K n hn p q h a i s = laurentRing K (Polynomial.toLaurent
      (((sectionEquiv K n hn p q h a 2 s).val i).val) * LaurentPolynomial.T (-1)) := by
  rw [torusRatio_def]
  exact torus_interior_ratio K n hn p q h a i s

/-- The quadratic branch coordinate restricts to the Laurent generator T. -/
lemma torusRatio_quadratic (i : Fin n) :
    torusRatio K n hn p q h a i (cubicFamily K n hn p q h a (.inr ⟨(i, 2)⟩)) =
      laurentRing K (LaurentPolynomial.T 1) := by
  have hp : (((sectionEquiv K n hn p q h a 2
      (cubicFamily K n hn p q h a (.inr ⟨(i, 2)⟩))).val i).val) = Polynomial.X ^ 2 := by
    change (((sectionEquiv K n hn p q h a 2
      (nodeSection K n hn p q h a _ _ _)).val i).val) = _
    rw [nodeSection_polynomial]
    simp [PolygonCubicInterpolation.cubic, cubicDelta,
      ← Polynomial.C_mul_X_pow_eq_monomial]
  rw [torusRatio_eq, hp, Polynomial.toLaurent_X_pow, ← LaurentPolynomial.T_add]
  rfl

/-- The node coordinate includes the self-incidence term, also for the one-gon. -/
lemma torusRatio_node (i : Fin n) :
    torusRatio K n hn p q h a i (cubicFamily K n hn p q h a (.inr ⟨(i, 0)⟩)) =
      laurentRing K (LaurentPolynomial.T (-1) +
        LaurentPolynomial.C (weight K n a 3 i * cubicDelta K n i 0 0 ((finRotate n).symm i)) *
          LaurentPolynomial.T 2) := by
  have hp : (((sectionEquiv K n hn p q h a 2
      (cubicFamily K n hn p q h a (.inr ⟨(i, 0)⟩))).val i).val) =
      1 + Polynomial.C (weight K n a 3 i *
        cubicDelta K n i 0 0 ((finRotate n).symm i)) * Polynomial.X ^ 3 := by
    change (((sectionEquiv K n hn p q h a 2
      (nodeSection K n hn p q h a _ _ _)).val i).val) = _
    rw [nodeSection_polynomial]
    simp [PolygonCubicInterpolation.cubic, cubicDelta,
      ← Polynomial.C_mul_X_pow_eq_monomial]
  rw [torusRatio_eq, hp]
  congr 1
  simp only [map_add, map_mul, map_one, Polynomial.toLaurent_C,
    Polynomial.toLaurent_X_pow, add_mul, one_mul, mul_assoc, ← LaurentPolynomial.T_add]
  rfl

end FLT.Mazur.PolygonCubicSections
