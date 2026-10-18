/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassChangeFullComparison
public import FLT.Mazur.WeierstrassGeneralizedSmoothComparison
public import FLT.Mazur.SmoothGeneralizedCurvePointedIso

/-!
# Full generalized comparisons and pointed Weierstrass comparisons

For smooth long equations the full DR isomorphisms are exactly the pointed
proper-curve isomorphisms. Forgetting or restoring the group and action loses
no comparison, over arbitrary coefficient rings.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry WeierstrassCurve
namespace FLT.Mazur.WeierstrassChangeParameter
open WeierstrassIntegralChart GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] (W V : WeierstrassCurve R)
  (hW : IsUnit W.Δ) (hV : IsUnit V.Δ)
local notation "E" => integralGeneralizedEllipticCurve W hW
local notation "F" => integralGeneralizedEllipticCurve V hV

/-- Forgetting a full DR comparison retains the whole pointed cubic map. -/
def generalizedToPointed (e : E ≅ F) : PointedComparison W V := by
  refine ⟨((forgetCurve).mapIso e |> (Over.forget _).mapIso), e.hom.curve.w, ?_⟩
  have h := e.hom.identitySection
  rw [integralGeneralizedEllipticCurve_identity,
    integralGeneralizedEllipticCurve_identity] at h
  exact congrArg (fun z ↦ z.left) h

/-- A pointed comparison preserves the original identity section in the over category. -/
theorem pointedComparison_identity (e : PointedComparison W V) :
    (E).identitySection ≫ (Over.isoMk e.val e.property.1).hom = (F).identitySection := by
  rw [integralGeneralizedEllipticCurve_identity,
    integralGeneralizedEllipticCurve_identity]
  apply Over.OverMorphism.ext
  exact e.property.2

/-- The prescribed pointed proper isomorphism extends to the original full models. -/
def pointedToGeneralized (e : PointedComparison W V) : E ≅ F := by
  let _ : Smooth (E).curve.hom := integralCurveStructure_smooth W hW
  let _ : Smooth (F).curve.hom := integralCurveStructure_smooth V hV
  exact pointedSmoothIso E F (Over.isoMk e.val e.property.1)
    (pointedComparison_identity W V hW hV e)

/-- Restoring the full model retains the exact original proper-curve morphism. -/
theorem pointedToGeneralized_curve (e : PointedComparison W V) :
    (pointedToGeneralized W V hW hV e).hom.curve.left = e.val.hom := by
  let _ : Smooth (E).curve.hom := integralCurveStructure_smooth W hW
  let _ : Smooth (F).curve.hom := integralCurveStructure_smooth V hV
  exact congrArg (fun z ↦ z.left) (pointedSmoothIso_curve E F
    (Over.isoMk e.val e.property.1) (pointedComparison_identity W V hW hV e))

/-- Full comparison is equivalent to pointed comparison without discarding automorphisms. -/
def generalizedPointedEquiv : (E ≅ F) ≃ PointedComparison W V where
  toFun := generalizedToPointed W V hW hV
  invFun := pointedToGeneralized W V hW hV
  left_inv e := by
    apply Iso.ext
    apply (forgetCurve).map_injective
    apply Over.OverMorphism.ext
    exact pointedToGeneralized_curve W V hW hV _
  right_inv e := by
    apply Subtype.ext
    apply Iso.ext
    exact pointedToGeneralized_curve W V hW hV e

end FLT.Mazur.WeierstrassChangeParameter
