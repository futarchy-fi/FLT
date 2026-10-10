/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.SchemeOpenPushoutCharts
public import FLT.Mazur.WeierstrassSuccessiveReplacementAtlas
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Assoc

/-!
# Exposing the next exterior in the actual replacement

Glue the retained exterior to the new x-direction chart first. Pushout
associativity identifies the resulting two-chart presentation with the
already constructed replacement, preserving all three chart inclusions.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s π c3 c4 c6 : R)
local notation "e" =>
  WeierstrassModificationX.xOpenInclusion W s (π * c3) (π * c4) (π ^ 2 * c6)

/-- The preceding overlap embeds directly into the new x-direction chart. -/
def replacementOverlapToX :
    Spec (.of (WeierstrassModificationX.XOpen W s (π * c3) (π * c4) (π ^ 2 * c6))) ⟶
      Spec (.of (Coordinate W s π c3 c4 c6)) :=
  (WeierstrassModificationX.overlapIso W s (π * c3) (π * c4) (π ^ 2 * c6)).hom ≫
    (horizontalIso W s π c3 c4 c6).inv ≫ horizontalOpenInclusion W s π c3 c4 c6

instance replacementOverlapToX_isOpenImmersion :
    IsOpenImmersion (replacementOverlapToX W s π c3 c4 c6) := by
  unfold replacementOverlapToX
  infer_instance

/-- Its inclusion in the local modification is the preceding replacement overlap. -/
@[reassoc] theorem replacementOverlapToX_chart :
    replacementOverlapToX W s π c3 c4 c6 ≫ xChart W s π c3 c4 c6 =
      replacementOverlap W s π c3 c4 c6 := by
  simp only [replacementOverlapToX, replacementOverlap, previousHorizontalChart, Category.assoc]

/-- The enlarged exterior includes the new x-direction chart. -/
def replacementNextExterior : Scheme := pushout e (replacementOverlapToX W s π c3 c4 c6)

/-- The deeper overlap embeds in that enlarged exterior. -/
def replacementNextOverlap : Spec (.of (XOpen W s π c3 c4 c6)) ⟶
    replacementNextExterior W s π c3 c4 c6 :=
  xOpenInclusion W s π c3 c4 c6 ≫ pushout.inr _ _

instance replacementNextOverlap_isOpenImmersion :
    IsOpenImmersion (replacementNextOverlap W s π c3 c4 c6) := by
  unfold replacementNextOverlap
  infer_instance

/-- The new exterior and deeper divided chart present the same whole replacement. -/
def replacementReassociation :
    pushout (replacementNextOverlap W s π c3 c4 c6)
      (overlapToDivided W s π c3 c4 c6) ≅ replacement W s π c3 c4 c6 :=
  (pushoutAssoc e (replacementOverlapToX W s π c3 c4 c6)
    (xOpenInclusion W s π c3 c4 c6) (overlapToDivided W s π c3 c4 c6)) ≪≫
      pushout.congrHom rfl (replacementOverlapToX_chart W s π c3 c4 c6)

/-- Reassociation preserves the retained exterior. -/
@[reassoc] theorem replacementReassociation_exterior :
    pushout.inl e (replacementOverlapToX W s π c3 c4 c6) ≫ pushout.inl _ _ ≫
        (replacementReassociation W s π c3 c4 c6).hom =
      replacementExterior W s π c3 c4 c6 := by
  simp [Iso.trans_hom,
    replacementReassociation, replacementNextOverlap, replacementExterior, xChart]

/-- Reassociation preserves the new x-direction chart. -/
@[reassoc] theorem replacementReassociation_x :
    pushout.inr e (replacementOverlapToX W s π c3 c4 c6) ≫ pushout.inl _ _ ≫
        (replacementReassociation W s π c3 c4 c6).hom =
      replacementXChart W s π c3 c4 c6 := by
  simp [Iso.trans_hom,
    replacementReassociation, replacementNextOverlap, replacementXChart,
    xChart, replacementInner]

/-- Reassociation preserves the actual deeper divided chart. -/
@[reassoc] theorem replacementReassociation_divided :
    pushout.inr (replacementNextOverlap W s π c3 c4 c6)
        (overlapToDivided W s π c3 c4 c6) ≫
        (replacementReassociation W s π c3 c4 c6).hom =
      replacementDividedChart W s π c3 c4 c6 := by
  simp [Iso.trans_hom,
    replacementReassociation, replacementNextOverlap, replacementDividedChart,
    dividedChart, replacementInner, xChart]

end FLT.Mazur.WeierstrassSuccessiveX
