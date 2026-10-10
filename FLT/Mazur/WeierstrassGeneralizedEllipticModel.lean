/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassGenusOneFamily
public import FLT.Mazur.WeierstrassIntegralGroup
public import FLT.Mazur.GeneralizedEllipticCurve

/-!
# The actual good-reduction Weierstrass elliptic model

For unit discriminant, the original cubic is its entire smooth locus.
The proved genus-one family and constructed commutative group law therefore
give the existing generalized-elliptic-curve interface. The action is the
original addition; the singular-fiber rotation condition is vacuous by smoothness.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [CommRing R] (W : WeierstrassCurve R)

/-- The bundled cubic retains its proved local finite presentation. -/
instance integralCurveOver_finitePresentation :
    LocallyOfFinitePresentation (integralCurveOver W).hom :=
  integralCurveStructure_finitePresentation W

/-- The actual relative smooth-locus inclusion is an isomorphism for unit discriminant. -/
theorem integralCurveSmoothInclusion_isIso (hΔ : IsUnit W.Δ) :
    IsIso (curveSmoothInclusion (integralCurveOver W)) := by
  let _ := integralCurveStructure_smooth W hΔ
  have hi : IsIso (integralCurveStructure W).smoothLocus.ι := by
    rw [Scheme.Hom.smoothLocus_eq_top]
    exact (integralCurve W).topIso.isIso_hom
  have : IsIso ((Over.forget (Spec (.of R))).map
      (curveSmoothInclusion (integralCurveOver W))) := hi
  exact isIso_of_reflects_iso _ (Over.forget (Spec (.of R)))

variable (hΔ : IsUnit W.Δ)

/-- The original cubic group is canonically its entire relative smooth locus. -/
def integralCurveSmoothIso : integralCurveOver W ≅ curveSmoothOpen (integralCurveOver W) := by
  let _ := integralCurveSmoothInclusion_isIso W hΔ
  exact (asIso (curveSmoothInclusion (integralCurveOver W))).symm

/-- The smooth comparison composed with inclusion is the identity on the original cubic. -/
@[reassoc (attr := simp)] theorem integralCurveSmoothIso_inclusion :
    (integralCurveSmoothIso W hΔ).hom ≫ curveSmoothInclusion (integralCurveOver W) = 𝟙 _ :=
  (integralCurveSmoothIso W hΔ).hom_inv_id

/-- Unit discriminant constructs the actual geometric elliptic model with its proved addition. -/
def integralGeneralizedEllipticCurve : GeneralizedEllipticCurve (Spec (.of R)) := by
  let _ := integralCurveCommGrpObj W hΔ
  let _ := integralCurveStructure_smooth W hΔ
  refine
    { curve := integralCurveOver W
      family := integralCurve_classifiedGenusOneFamily W hΔ
      group := integralCurveOver W
      smoothIso := integralCurveSmoothIso W hΔ
      act := μ[integralCurveOver W]
      unit_act := MonObj.one_mul _
      assoc_act := MonObj.mul_assoc _
      restriction := ?_
      rotations := ?_ }
  · rw [integralCurveSmoothIso_inclusion, whiskerLeft_id, Category.id_comp, Category.comp_id]
  · intro K _ _ s hs
    exact hs (inferInstanceAs (Smooth (pullback.snd (integralCurveStructure W) s))) |>.elim

/-- The constructed geometric model has the original cubic as its curve. -/
theorem integralGeneralizedEllipticCurve_curve :
    (integralGeneralizedEllipticCurve W hΔ).curve = integralCurveOver W := rfl

/-- Its group action is precisely the regular addition constructed on that cubic. -/
theorem integralGeneralizedEllipticCurve_action :
    (integralGeneralizedEllipticCurve W hΔ).act = integralCurveOverAddition W hΔ := rfl

end FLT.Mazur.WeierstrassIntegralChart
