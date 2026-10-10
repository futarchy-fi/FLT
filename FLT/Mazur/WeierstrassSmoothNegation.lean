/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothZeroSection
public import FLT.Mazur.WeierstrassGlobalNegationInvolution

/-!
# Negation on the relative smooth locus

The original global involution is an automorphism over the base, hence
preserves the actual smooth locus. Its restriction remains involutive and
fixes the constructed zero section for every Weierstrass equation.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The original negation automorphism preserves the relative smooth locus exactly. -/
theorem integralCurveNegation_preimage_smooth :
    integralCurveNegation W ⁻¹ᵁ integralSmoothOpen W = integralSmoothOpen W := by
  let _ : IsIso (integralCurveNegation W) := (integralCurveNegationIso W).isIso_hom
  simp only [integralSmoothOpen, Scheme.Hom.preimage_smoothLocus_eq,
    integralCurveNegation_structure]

/-- Restrict the original global negation to the actual relative smooth open. -/
def integralSmoothNegation : (integralSmoothOpen W).toScheme ⟶
    (integralSmoothOpen W).toScheme :=
  IsOpenImmersion.lift (integralSmoothOpen W).ι
    ((integralSmoothOpen W).ι ≫ integralCurveNegation W) (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨x, rfl⟩
      have h : x.val ∈
          integralCurveNegation W ⁻¹ᵁ integralSmoothOpen W := by
        rw [integralCurveNegation_preimage_smooth]
        exact x.property
      exact h)

/-- The restricted operation retains the actual cubic negation. -/
@[reassoc (attr := simp)] theorem integralSmoothNegation_inclusion :
    integralSmoothNegation W ≫ (integralSmoothOpen W).ι =
      (integralSmoothOpen W).ι ≫ integralCurveNegation W :=
  IsOpenImmersion.lift_fac _ _ _

/-- Restricted negation is still defined over the original coefficient ring. -/
@[reassoc] theorem integralSmoothNegation_structure :
    integralSmoothNegation W ≫ integralSmoothStructure W = integralSmoothStructure W := by
  rw [integralSmoothStructure, ← Category.assoc, integralSmoothNegation_inclusion,
    Category.assoc, integralCurveNegation_structure]

/-- Negation is an involution on the actual smooth locus. -/
@[reassoc (attr := simp)] theorem integralSmoothNegation_comp :
    integralSmoothNegation W ≫ integralSmoothNegation W = 𝟙 _ := by
  apply (cancel_mono (integralSmoothOpen W).ι).mp
  simp only [Category.assoc, integralSmoothNegation_inclusion, Category.id_comp,
    integralSmoothNegation_inclusion_assoc, integralCurveNegation_comp, Category.comp_id]

/-- The restricted involution is an actual scheme automorphism. -/
def integralSmoothNegationIso : (integralSmoothOpen W).toScheme ≅
    (integralSmoothOpen W).toScheme where
  hom := integralSmoothNegation W
  inv := integralSmoothNegation W
  hom_inv_id := integralSmoothNegation_comp W
  inv_hom_id := integralSmoothNegation_comp W

/-- The smooth zero section is fixed by the restricted negation. -/
@[reassoc (attr := simp)] theorem integralSmoothZero_negation :
    integralSmoothZero W ≫ integralSmoothNegation W = integralSmoothZero W := by
  apply (cancel_mono (integralSmoothOpen W).ι).mp
  simp only [Category.assoc, integralSmoothNegation_inclusion,
    integralSmoothZero_inclusion_assoc, integralCurveZero_negation,
    integralSmoothZero_inclusion]

end FLT.Mazur.WeierstrassIntegralChart
