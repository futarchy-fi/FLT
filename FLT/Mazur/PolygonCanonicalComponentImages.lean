/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCanonicalComponentRatios
public import FLT.Mazur.PolygonCubicFiniteFamily

/-!
# Interpolation images with the canonical denominator

Compute ratios of the actual compared component sections on the marked affine
normalization branches. The node-value coordinate retains the cyclic self-incidence term;
these branch calculations do not assert surjectivity at the pinched node.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open scoped Polynomial
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonCubicSections
open FCurve PolygonPinching PolygonPowerNodeEndpoints
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Fin n → Kˣ)

/-- The actual compared component ratio in the localized normalization coordinate ring. -/
irreducible_def canonicalComponentRatio (i : Fin n)
    (s : Γ(polygonLine K n hn p q h a 3, ⊤)) :
    ProjectiveLineCanonicalRatios.ring K (a i) :=
  let := ProjectiveLineCanonicalRatios.toLine_canonical_isIso K (a i) 3
  (ProjectiveLineCanonicalRatios.coordinates K (a i)).symm
    (pullbackSectionRatio (ProjectiveLineCanonicalRatios.toLine K (a i))
      (ProjectiveLineMarkedSectionTransition.line K (a i) 3)
      (divisorSection ((ProjectiveLineMarkedCharts.relativeCartier K (a i)).1.pow 3) ⊤)
      (componentSection K n hn p q h a s i))

/-- The sealed actual ratio is P/(X-a)^3. -/
lemma canonicalComponentRatio_eq (i : Fin n)
    (s : Γ(polygonLine K n hn p q h a 3, ⊤)) :
    canonicalComponentRatio K n hn p q h a i s =
      algebraMap K[X] (ProjectiveLineCanonicalRatios.ring K (a i))
        (((sectionEquiv K n hn p q h a 2 s).val i).val) *
        IsLocalization.Away.invSelf (Polynomial.X - Polynomial.C (a i : K)) ^ 3 := by
  rw [canonicalComponentRatio_def]
  dsimp only
  rw [sealed_component_canonical_ratio, RingEquiv.symm_apply_apply]

/-- The linear interpolation coordinate has its exact canonical-denominator image. -/
lemma canonicalComponentRatio_linear (i : Fin n) :
    canonicalComponentRatio K n hn p q h a i (cubicFamily K n hn p q h a (.inr ⟨(i, 1)⟩)) =
      algebraMap K[X] (ProjectiveLineCanonicalRatios.ring K (a i)) Polynomial.X *
        IsLocalization.Away.invSelf (Polynomial.X - Polynomial.C (a i : K)) ^ 3 := by
  rw [canonicalComponentRatio_eq]
  congr 2
  change (((sectionEquiv K n hn p q h a 2 (nodeSection K n hn p q h a _ _ _)).val i).val) = _
  rw [nodeSection_polynomial]
  simp [PolygonCubicInterpolation.cubic, cubicDelta, ← Polynomial.C_mul_X_pow_eq_monomial]

/-- The quadratic interpolation coordinate has its exact canonical-denominator image. -/
lemma canonicalComponentRatio_quadratic (i : Fin n) :
    canonicalComponentRatio K n hn p q h a i (cubicFamily K n hn p q h a (.inr ⟨(i, 2)⟩)) =
      algebraMap K[X] (ProjectiveLineCanonicalRatios.ring K (a i)) (Polynomial.X ^ 2) *
        IsLocalization.Away.invSelf (Polynomial.X - Polynomial.C (a i : K)) ^ 3 := by
  rw [canonicalComponentRatio_eq]
  congr 2
  change (((sectionEquiv K n hn p q h a 2 (nodeSection K n hn p q h a _ _ _)).val i).val) = _
  rw [nodeSection_polynomial]
  simp [PolygonCubicInterpolation.cubic, cubicDelta, ← Polynomial.C_mul_X_pow_eq_monomial]

/-- Self-incidence contributes a cubic numerator term to the node-value coordinate. -/
lemma canonicalComponentRatio_node (i : Fin n) :
    canonicalComponentRatio K n hn p q h a i (cubicFamily K n hn p q h a (.inr ⟨(i, 0)⟩)) =
      algebraMap K[X] (ProjectiveLineCanonicalRatios.ring K (a i))
        (1 + Polynomial.C (weight K n a 3 i * cubicDelta K n i 0 0 ((finRotate n).symm i)) *
          Polynomial.X ^ 3) *
        IsLocalization.Away.invSelf (Polynomial.X - Polynomial.C (a i : K)) ^ 3 := by
  rw [canonicalComponentRatio_eq]
  congr 2
  change (((sectionEquiv K n hn p q h a 2 (nodeSection K n hn p q h a _ _ _)).val i).val) = _
  rw [nodeSection_polynomial]
  simp [PolygonCubicInterpolation.cubic, cubicDelta, ← Polynomial.C_mul_X_pow_eq_monomial]

end FLT.Mazur.PolygonCubicSections
