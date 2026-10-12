/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliaryNormalizationGroup
public import FLT.Mazur.UniversalWeierstrassNormalizedSliceFixed
public import FLT.Mazur.WeierstrassVariableChangeIdentity

/-!
# The actual normalization group map fixes a normalized frame

On the closed normalized frame, the complete proper group comparison is the
canonical equality isomorphism. This controls every section of the group,
including labels outside the auxiliary marking.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry WeierstrassCurve MonoidalCategory
namespace FLT.Mazur.UniversalWeierstrass
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] integralCurveGroup integralVariableChangeGroupIso
variable {R : Type} [CommRing R]

/-- An identity admissible change gives the equality isomorphism of the actual groups. -/
theorem normalizationGroupIso_of_identity (W V : WeierstrassCurve R)
    (C : VariableChange R) (h : C • W = V) (hW : IsUnit W.Δ) (hV : IsUnit V.Δ)
    (hC : C = 1) (hG : integralCurveGroup V hV = integralCurveGroup W hW) :
    integralVariableChangeGroupIso W V C h hW hV = eqToIso hG := by
  subst C
  have hVeq : V = W := h.symm.trans (one_smul _ _)
  cases hVeq
  exact integralVariableChangeGroupIso_one W hW

variable (g : AuxiliarySectionRing →+* R) (hn : SatisfiesNormalization g)

include hn in
/-- The entire normalized group equals the original group on the normalized frame. -/
theorem auxiliaryNormalizedGroup_fixed : auxiliaryNormalizedGroup g = auxiliaryPullbackGroup g := by
  unfold auxiliaryNormalizedGroup auxiliaryPullbackGroup
  congr 1
  exact normalizedSlice_equation_fixed g hn

/-- Normalization fixes the actual proper group, not just its auxiliary marked sections. -/
theorem auxiliaryNormalizationGroupIso_fixed :
    auxiliaryNormalizationGroupIso g = eqToIso (auxiliaryNormalizedGroup_fixed g hn) := by
  exact normalizationGroupIso_of_identity _ _ _ _ _ _
    (normalizedSlice_frameChange g hn) (auxiliaryNormalizedGroup_fixed g hn)

/-- Every section is fixed after identifying the normalized and original groups. -/
theorem auxiliaryNormalizationGroupIso_fixed_section
    (s : 𝟙_ (Over (Spec (.of R))) ⟶ (auxiliaryNormalizedGroup g).X) :
    s ≫ (auxiliaryNormalizationGroupIso g).hom.hom.hom.hom =
      s ≫ (eqToIso (auxiliaryNormalizedGroup_fixed g hn)).hom.hom.hom.hom := by
  rw [auxiliaryNormalizationGroupIso_fixed g hn]

end FLT.Mazur.UniversalWeierstrass
