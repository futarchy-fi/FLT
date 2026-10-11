/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLeftSmoothSectionTranslation

/-!
# Translation preserves the original smooth and singular loci

The actual translation is an automorphism over the original coefficients.
Consequently its inverse image preserves the entire relative smooth open,
with no discriminant assumption. The complementary point statement concerns
singular support, not an assertion about a scheme-theoretic modification ideal.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
  (a : Spec (.of R) ⟶ (integralSmoothOpen W).toScheme)
  (ha : a ≫ integralSmoothStructure W = 𝟙 _)

/-- Translation by an actual smooth section preserves the full original smooth open exactly. -/
theorem integralCurveTranslation_preimage_smooth :
    integralCurveTranslation W a ha ⁻¹ᵁ integralSmoothOpen W = integralSmoothOpen W := by
  let _ : IsIso (integralCurveTranslation W a ha) := (integralCurveTranslationIso W a ha).isIso_hom
  simp only [integralSmoothOpen, Scheme.Hom.preimage_smoothLocus_eq,
    integralCurveTranslation_structure]

/-- Smoothness of an original point is equivalent to smoothness of its actual translate. -/
theorem integralCurveTranslation_mem_smooth (x : integralCurve W) :
    integralCurveTranslation W a ha x ∈ integralSmoothOpen W ↔ x ∈ integralSmoothOpen W := by
  change x ∈ integralCurveTranslation W a ha ⁻¹ᵁ integralSmoothOpen W ↔ _
  rw [integralCurveTranslation_preimage_smooth]

/-- The actual translation preserves singular support in both directions. -/
theorem integralCurveTranslation_mem_singular (x : integralCurve W) :
    integralCurveTranslation W a ha x ∉ integralSmoothOpen W ↔ x ∉ integralSmoothOpen W :=
  not_congr (integralCurveTranslation_mem_smooth W a ha x)

/-- At a coefficient fiber with a unique nonsmooth point, translation fixes that point. -/
theorem integralCurveTranslation_fixes_unique_singular (x : integralCurve W)
    (hx : x ∉ integralSmoothOpen W)
    (hunique : ∀ y : integralCurve W, y ∉ integralSmoothOpen W →
      integralCurveStructure W y = integralCurveStructure W x → y = x) :
    integralCurveTranslation W a ha x = x := by
  apply hunique _ ((integralCurveTranslation_mem_singular W a ha x).mpr hx)
  exact congrArg (fun f : integralCurve W ⟶ Spec (.of R) => f x)
    (integralCurveTranslation_structure W a ha)

end FLT.Mazur.WeierstrassIntegralChart
