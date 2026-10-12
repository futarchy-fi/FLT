/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationSaturationKernel

/-!
# Original relation composition acts on the saturation cover

Pull the original saturated relation back along its first endpoint cover.
Composition then lifts its second endpoint to the same cover and keeps the
unchanged generating endpoint. This supplies scheme-level invariance witnesses.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme.{u}} {A U : Over S} {p q : A ⟶ U}
  (e : CategoryTheory.EquivalenceRelation p q) (hq : IsOpenMap q.left)
  (W : U.left.Opens)
local notation "Z" => Subtype.val (saturateOpen e hq W)
local notation "g" => saturationCover e hq W
local notation "h" => saturationGeneratorProjection (p := p) W

/-- The first endpoint of the unchanged saturated relation. -/
def saturatedRelationFst : (p.left ⁻¹ᵁ Z).toScheme ⟶ (Z).toScheme :=
  p.left.resLE Z _ le_rfl

/-- The second endpoint uses the proved invariance of the saturation. -/
def saturatedRelationSnd : (p.left ⁻¹ᵁ Z).toScheme ⟶ (Z).toScheme :=
  q.left.resLE Z _ (saturateOpen_preimage_eq e hq W).le

/-- The generating arrow domain is the actual first-endpoint pullback. -/
theorem saturationGenerator_isPullback :
    IsPullback (p.left ⁻¹ᵁ W).ι h p.left W.ι := by
  rw [saturationGeneratorProjection, Scheme.Hom.resLE_eq_morphismRestrict]
  exact (isPullback_morphismRestrict p.left W).flip

local notation "P" => saturatedRelationFst e hq W
local notation "Q" => saturatedRelationSnd e hq W

/-- The two original arrows on the relation cover are composable. -/
theorem saturationAction_composable :
    (pullback.fst g P ≫ (p.left ⁻¹ᵁ W).ι) ≫ q.left =
      (pullback.snd g P ≫ (p.left ⁻¹ᵁ Z).ι) ≫ p.left := by
  rw [Category.assoc, ← saturationCover_comp_ι e hq W, ← Category.assoc,
    pullback.condition, Category.assoc, saturatedRelationFst, Scheme.Hom.resLE_comp_ι,
    Category.assoc]

/-- Compose the unchanged original arrows on the relation cover. -/
def saturationActionArrow : pullback g P ⟶ A.left :=
  composeOriginal e (pullback.fst g P ≫ (p.left ⁻¹ᵁ W).ι)
    (pullback.snd g P ≫ (p.left ⁻¹ᵁ Z).ι) (saturationAction_composable e hq W)

/-- Composition lifts the new second endpoint to the original saturation cover. -/
def saturationAction : pullback g P ⟶ (p.left ⁻¹ᵁ W).toScheme :=
  (saturationGenerator_isPullback W).lift (saturationActionArrow e hq W)
    (pullback.fst g P ≫ h) (by
      rw [saturationActionArrow, composeOriginal_fst, Category.assoc, Category.assoc,
        saturationGeneratorProjection, Scheme.Hom.resLE_comp_ι])

@[reassoc]
theorem saturationAction_original :
    saturationAction e hq W ≫ (p.left ⁻¹ᵁ W).ι = saturationActionArrow e hq W :=
  (saturationGenerator_isPullback W).lift_fst _ _ _

@[reassoc]
theorem saturationAction_generator :
    saturationAction e hq W ≫ h = pullback.fst g P ≫ h :=
  (saturationGenerator_isPullback W).lift_snd _ _ _

/-- The composed lift covers the second endpoint of the original saturated relation. -/
@[reassoc]
theorem saturationAction_cover : saturationAction e hq W ≫ g = pullback.snd g P ≫ Q := by
  apply (cancel_mono (Z).ι).mp
  rw [Category.assoc, saturationCover_comp_ι, ← Category.assoc,
    saturationAction_original, saturationActionArrow, composeOriginal_snd,
    Category.assoc, Category.assoc, saturatedRelationSnd, Scheme.Hom.resLE_comp_ι]

end FLT.Mazur.RelativeRelationOrbit
