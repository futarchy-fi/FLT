/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GroupObjectPointTranslation
public import FLT.Mazur.WeierstrassOriginIsomorphismGroup

/-!
# Normalizing an actual cubic automorphism at infinity

Translate by the inverse image of infinity. The resulting original scheme
isomorphism fixes infinity, so the established classification makes it a
group isomorphism. Triviality of this group automorphism remains separate.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.MonObj
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] GroupObjectPointTranslation.translation
  GroupObjectPointTranslation.normalizedIso

variable {R : Type} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)
  (e : integralCurve W ≅ integralCurve W)
  (hb : e.hom ≫ integralCurveStructure W = integralCurveStructure W)

/-- The given scheme automorphism with its proved original base compatibility. -/
def curveAutomorphismOverIso : integralCurveOver W ≅ integralCurveOver W := Over.isoMk e hb

/-- The normalized automorphism is constructed in the original slice category. -/
def normalizedCurveOverIso : integralCurveOver W ≅ integralCurveOver W := by
  let _ := integralCurveCommGrpObj W hΔ
  exact GroupObjectPointTranslation.normalizedIso (curveAutomorphismOverIso W e hb)

/-- The original automorphism is recovered by its group part and actual infinity image. -/
theorem normalizedCurveOverIso_recover :
    let _ := integralCurveCommGrpObj W hΔ
    (normalizedCurveOverIso W hΔ e hb).hom ≫
      GroupObjectPointTranslation.translation
        ((1 : 𝟙_ (Over (Spec (.of R))) ⟶ integralCurveOver W) ≫
          (curveAutomorphismOverIso W e hb).hom) =
      (curveAutomorphismOverIso W e hb).hom := by
  let _ := integralCurveCommGrpObj W hΔ
  exact GroupObjectPointTranslation.normalizedIso_translation (curveAutomorphismOverIso W e hb)

/-- Forgetting the base gives the same actual normalized scheme isomorphism. -/
def normalizedCurveIso : integralCurve W ≅ integralCurve W :=
  (Over.forget _).mapIso (normalizedCurveOverIso W hΔ e hb)

/-- The normalized isomorphism preserves the original coefficient spectrum. -/
@[reassoc] theorem normalizedCurveIso_over :
    (normalizedCurveIso W hΔ e hb).hom ≫ integralCurveStructure W =
      integralCurveStructure W := (normalizedCurveOverIso W hΔ e hb).hom.w

/-- Translating by the inverse of the original infinity image fixes infinity exactly. -/
@[reassoc] theorem normalizedCurveIso_zero :
    integralCurveZero W ≫ (normalizedCurveIso W hΔ e hb).hom = integralCurveZero W := by
  let _ := integralCurveCommGrpObj W hΔ
  have he := GroupObjectPointTranslation.normalizedIso_one (curveAutomorphismOverIso W e hb)
  have hz := congrArg (fun f : 𝟙_ (Over (Spec (.of R))) ⟶ integralCurveOver W ↦ f.left) he
  change integralCurveZero W ≫ (normalizedCurveIso W hΔ e hb).hom = integralCurveZero W
  change (𝟙 _ ≫ integralCurveZero W) ≫ (normalizedCurveIso W hΔ e hb).hom =
    𝟙 _ ≫ integralCurveZero W at hz
  simpa only [Category.id_comp] using hz

/-- The constructed normalized automorphism respects the established elliptic group law. -/
def normalizedCurveGroupIso : integralCurveGroup W hΔ ≅ integralCurveGroup W hΔ :=
  originIsoGroupIso W W hΔ hΔ (normalizedCurveIso W hΔ e hb)
    (normalizedCurveIso_over W hΔ e hb) (normalizedCurveIso_zero W hΔ e hb)

/-- The group upgrade retains the actual normalized scheme morphism. -/
theorem normalizedCurveGroupIso_hom :
    (normalizedCurveGroupIso W hΔ e hb).hom.hom.hom.hom.left =
      (normalizedCurveIso W hΔ e hb).hom := rfl

end FLT.Mazur.WeierstrassIntegralChart
