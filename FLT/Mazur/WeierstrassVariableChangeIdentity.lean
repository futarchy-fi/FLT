/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassVariableChangeGroup

/-!
# Identity admissible changes fix the entire proper group family

The identity coordinate change induces the identity ambient projective map,
proper cubic map, and group isomorphism. These are scheme equalities over any
coefficient ring, needed for normalization retraction on complete markings.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry WeierstrassCurve
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R]

/-- The identity admissible change induces the identity free-module equivalence. -/
theorem integralVariableChangeLinear_one :
    WeierstrassVariableChangeLinear.linearEquiv (1 : VariableChange R) =
      LinearEquiv.refl R (Fin 3 →₀ R) := by
  apply LinearEquiv.toLinearMap_injective
  exact WeierstrassVariableChangeLinear.linearMap_one

/-- The ambient projective scheme map of the identity admissible change is the identity. -/
theorem integralVariableChangeProjective_one :
    WeierstrassVariableChangeLinear.projectiveIso (1 : VariableChange R) = Iso.refl _ := by
  rw [WeierstrassVariableChangeLinear.projectiveIso, integralVariableChangeLinear_one]
  exact ProjectiveSpace.linearIso_refl

/-- The identity change induces the identity morphism of the entire original proper cubic. -/
theorem integralVariableChangeTo_one (W : WeierstrassCurve R) :
    integralVariableChangeTo W W 1 (one_smul _ _) = 𝟙 (integralCurve W) := by
  apply (cancel_mono (integralProjectiveMap W)).mp
  rw [integralVariableChangeTo_projectiveMap, integralVariableChangeProjective_one]
  exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- The proper-cubic isomorphism for the identity change is the actual identity isomorphism. -/
theorem integralVariableChangeIso_one (W : WeierstrassCurve R) :
    integralVariableChangeIso W W 1 (one_smul _ _) = Iso.refl _ := by
  apply Iso.ext
  exact integralVariableChangeTo_one W

/-- The identity admissible change is the identity isomorphism of the original group scheme. -/
theorem integralVariableChangeGroupIso_one (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ) :
    integralVariableChangeGroupIso W W 1 (one_smul _ _) hΔ hΔ = Iso.refl _ := by
  apply Iso.ext
  apply CommGrp.hom_ext
  apply Over.OverMorphism.ext
  exact integralVariableChangeTo_one W

end FLT.Mazur.WeierstrassIntegralChart
