/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXHorizontalScheme
public import FLT.Mazur.WeierstrassModificationGluing

/-!
# Replacing the divided chart in the preceding whole modification

The outer x-chart is retained. Its original overlap with the preceding divided
chart embeds into the new local step by the proved horizontal comparison.
Gluing along this actual open immersion constructs the next whole scheme and
a contraction back to the preceding whole modification.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s π c3 c4 c6 : R)
local notation "E" => WeierstrassModificationX.Coordinate W s (π * c3) (π * c4) (π ^ 2 * c6)
local notation "O" => WeierstrassModificationX.XOpen W s (π * c3) (π * c4) (π ^ 2 * c6)
local notation "P" => WeierstrassModificationX.modification W s (π * c3) (π * c4) (π ^ 2 * c6)

/-- The original outer overlap embeds into the new local step via the unchanged open. -/
def replacementOverlap : Spec (.of O) ⟶ modification W s π c3 c4 c6 :=
  (WeierstrassModificationX.overlapIso W s (π * c3) (π * c4) (π ^ 2 * c6)).hom ≫
    previousHorizontalChart W s π c3 c4 c6

instance replacementOverlap_isOpenImmersion :
    IsOpenImmersion (replacementOverlap W s π c3 c4 c6) := by
  unfold replacementOverlap
  infer_instance

/-- The unchanged overlap retains its original map into the preceding divided chart. -/
@[reassoc] theorem replacementOverlap_contraction :
    replacementOverlap W s π c3 c4 c6 ≫ contraction W s π c3 c4 c6 =
      WeierstrassModificationX.overlapToDivided W s (π * c3) (π * c4) (π ^ 2 * c6) := by
  simp only [replacementOverlap, Category.assoc, previousHorizontalChart_contraction]
  rfl

/-- The actual scheme obtained by replacing the preceding divided chart with its local step. -/
def replacement : Scheme :=
  pushout (WeierstrassModificationX.xOpenInclusion W s (π * c3) (π * c4) (π ^ 2 * c6))
    (replacementOverlap W s π c3 c4 c6)

/-- The unchanged exterior chart of the replacement. -/
def replacementExterior : Spec (.of E) ⟶ replacement W s π c3 c4 c6 := pushout.inl _ _

/-- The actual new local step as an open subscheme of the replacement. -/
def replacementInner : modification W s π c3 c4 c6 ⟶ replacement W s π c3 c4 c6 :=
  pushout.inr _ _

instance replacementExterior_isOpenImmersion :
    IsOpenImmersion (replacementExterior W s π c3 c4 c6) := by
  change IsOpenImmersion (colimit.ι
    (span (WeierstrassModificationX.xOpenInclusion W s (π * c3) (π * c4) (π ^ 2 * c6))
      (replacementOverlap W s π c3 c4 c6)) WalkingSpan.left)
  infer_instance

instance replacementInner_isOpenImmersion :
    IsOpenImmersion (replacementInner W s π c3 c4 c6) := by
  change IsOpenImmersion (colimit.ι
    (span (WeierstrassModificationX.xOpenInclusion W s (π * c3) (π * c4) (π ^ 2 * c6))
      (replacementOverlap W s π c3 c4 c6)) WalkingSpan.right)
  infer_instance

/-- The two inclusions identify the actual preceding overlap. -/
@[reassoc] theorem replacement_chart_overlap :
    WeierstrassModificationX.xOpenInclusion W s (π * c3) (π * c4) (π ^ 2 * c6) ≫
        replacementExterior W s π c3 c4 c6 =
      replacementOverlap W s π c3 c4 c6 ≫ replacementInner W s π c3 c4 c6 :=
  pushout.condition

/-- The actual replacement contracts to the preceding whole modification. -/
def replacementContraction : replacement W s π c3 c4 c6 ⟶ P :=
  pushout.desc (WeierstrassModificationX.xChart W s (π * c3) (π * c4) (π ^ 2 * c6))
    (contraction W s π c3 c4 c6 ≫
      WeierstrassModificationX.dividedChart W s (π * c3) (π * c4) (π ^ 2 * c6)) (by
        rw [← Category.assoc, replacementOverlap_contraction]
        exact WeierstrassModificationX.chart_overlap W s (π * c3) (π * c4) (π ^ 2 * c6))

/-- The whole contraction is unchanged on the exterior chart. -/
@[reassoc (attr := simp)] theorem replacementExterior_contraction :
    replacementExterior W s π c3 c4 c6 ≫ replacementContraction W s π c3 c4 c6 =
      WeierstrassModificationX.xChart W s (π * c3) (π * c4) (π ^ 2 * c6) :=
  pushout.inl_desc _ _ _

/-- On the new local step it is the actual local contraction followed by the old inclusion. -/
@[reassoc (attr := simp)] theorem replacementInner_contraction :
    replacementInner W s π c3 c4 c6 ≫ replacementContraction W s π c3 c4 c6 =
      contraction W s π c3 c4 c6 ≫
        WeierstrassModificationX.dividedChart W s (π * c3) (π * c4) (π ^ 2 * c6) :=
  pushout.inr_desc _ _ _

end FLT.Mazur.WeierstrassSuccessiveX
