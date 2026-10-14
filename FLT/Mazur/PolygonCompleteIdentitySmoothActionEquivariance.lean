/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentitySmoothActionCoordinates
public import FLT.Mazur.PolygonCompleteGenericMapIdentity

/-!
# Contraction equivariance on the entire original smooth polygon

Equality on the full identity preimage extends by flatness and separatedness.
The resulting equation includes every smooth point on contracted components.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic completeRotation
attribute [local instance] exactVeroneseProjToBase_lfp
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "S" => Spec (CommRingCat.of (PowerSeries K))
local notation "G" => completePointOriginalBaseGroup K n h (0 : Fin n)
local notation "M" => completeOriginalSmoothOver K n h
local notation "π" => exactVeroneseProjToBase K n h
local notation "U" => completePointIdentityOpen K n h (0 : Fin n)
local notation "W" => completePointWeierstrassCurve K n h (0 : Fin n)
local notation "g" => completePointToIntegralCubic K n h (0 : Fin n)
local notation "j" => completeIdentityChart K n h (0 : Fin n) 0
local notation "p" => completeIdentitySmoothSecond K n h
local notation "V" => completeIdentitySmoothActionCoordinateOpen K n h
local notation "l" => completeIdentitySmoothActionCoordinates K n h

/-- The whole smooth action source is flat over the unchanged original base. -/
theorem completeIdentitySmoothActionSource_flat : Flat ((p) ≫ (π)) := by
  let _ := exactVeroneseProjToBase_flat K n h
  let _ : Flat (G).X.hom := by
    rw [completePointOriginalBaseGroup_structure]
    infer_instance
  change Flat ((pullback.snd (G).X.hom (M).hom ≫ (π).smoothLocus.ι) ≫ (π))
  infer_instance

/-- The constructed smooth action is equivariant for the original whole contraction. -/
@[reassoc] theorem completeIdentitySmoothAction_contraction :
    (completeIdentitySmoothAction K n h).left ≫ (π).smoothLocus.ι ≫ (g) =
      completeIdentitySmoothActionInput K n h ≫ completeIdentityActionTarget K n h 0 := by
  let _ := completeIdentitySmoothActionSource_flat K n h
  let v := integralCurveStructure (W) ≫ inv (S).toSpecΓ
  let _ : IsSeparated v := by dsimp only [v]; infer_instance
  apply completeFlat_identityPreimage_ext K n h 0 (p) v
  · apply (cancel_mono (S).toSpecΓ).mp
    simp only [v, Category.assoc, IsIso.inv_hom_id, Category.comp_id,
      completePointToIntegralCubic_over, completeIdentityActionTarget_structure,
      completeIdentitySmoothActionInput_snd_assoc]
    have hb : (completeIdentitySmoothAction K n h).left ≫ (M).hom =
        pullback.snd (G).X.hom (M).hom ≫ (M).hom :=
      (completeIdentitySmoothAction K n h).w.trans pullback.condition
    simpa only [completeOriginalSmoothOver, Over.mk_hom, Category.assoc] using
      congrArg (· ≫ (S).toSpecΓ) hb
  · change (V).ι ≫ _ = (V).ι ≫ _
    rw [← completeIdentitySmoothActionCoordinates_inclusion K n h]
    simp only [Category.assoc]
    have he := congrArg Over.Hom.left (completeIdentitySmoothAction_identity K n h)
    change (𝟙 (G).X ⊗ₘ (j)).left ≫ (completeIdentitySmoothAction K n h).left =
      (μ[(G).X]).left ≫ (j).left at he
    rw [← Category.assoc _ (completeIdentitySmoothAction K n h).left _, he,
      Category.assoc, completeIdentityChart_zero_inclusion_assoc,
      completeIdentitySmoothActionInput_identity_assoc, completeIdentityPairToAction_target]

end FLT.Mazur.PolygonInfinitesimalStages
