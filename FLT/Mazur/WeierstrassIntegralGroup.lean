/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIntegralGroupOperations
public import FLT.Mazur.WeierstrassIntegralAssociativity
public import FLT.Mazur.WeierstrassIntegralAdditionCommutative
public import FLT.Mazur.WeierstrassGlobalAdditionIdentity
public import FLT.Mazur.WeierstrassGlobalAdditionInverse
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_

/-!
# The integral Weierstrass commutative group scheme

For unit discriminant the actual glued cubic, with its constructed global
operations, is a commutative group object over the coefficient spectrum.
Every law comes from the established scheme morphism identities.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

/-- The global operations satisfy the monoid laws in the category over the base. -/
@[instance_reducible] def integralCurveMonObj : MonObj (integralCurveOver W) where
  one := integralCurveOverZero W
  mul := integralCurveOverAddition W hΔ
  one_mul := by
    apply (cancel_epi (λ_ (integralCurveOver W)).inv).mp
    apply Over.OverMorphism.ext
    change (_ ≫ _) ≫ integralCurveAddition W hΔ = _
    rw [integralCurveOver_leftZero, integralCurveAddition_left_identity]
    exact congrArg Over.Hom.left (Iso.inv_hom_id (λ_ (integralCurveOver W))).symm
  mul_one := by
    apply (cancel_epi (ρ_ (integralCurveOver W)).inv).mp
    apply Over.OverMorphism.ext
    change (_ ≫ _) ≫ integralCurveAddition W hΔ = _
    rw [integralCurveOver_rightZero, integralCurveAddition_right_identity]
    exact congrArg Over.Hom.left (Iso.inv_hom_id (ρ_ (integralCurveOver W))).symm
  mul_assoc := by
    apply Over.OverMorphism.ext
    change (integralCurveOverAddition W hΔ ▷ integralCurveOver W).left ≫
      integralCurveAddition W hΔ = _
    rw [integralCurveOver_addFirst]
    change _ = _ ≫ _ ≫ integralCurveAddition W hΔ
    rw [← Category.assoc, integralCurveOver_addLast]
    exact integralCurveAddition_assoc W hΔ

/-- The constructed global negation supplies both inverse laws. -/
@[instance_reducible] def integralCurveGrpObj : GrpObj (integralCurveOver W) where
  __ := integralCurveMonObj W hΔ
  inv := integralCurveOverNegation W
  left_inv := by
    apply Over.OverMorphism.ext
    exact integralCurveAddition_left_inverse W hΔ
  right_inv := by
    apply Over.OverMorphism.ext
    exact integralCurveAddition_right_inverse W hΔ

/-- The regular addition is commutative as a group object. -/
@[instance_reducible] def integralCurveCommGrpObj : CommGrpObj (integralCurveOver W) where
  __ := integralCurveGrpObj W hΔ
  mul_comm := by
    apply Over.OverMorphism.ext
    exact integralCurveAddition_commutative W hΔ

/-- The bundled integral commutative group scheme, with no assumed group laws. -/
def integralCurveGroup : CommGrp (Over (Spec (.of R))) := by
  letI := integralCurveCommGrpObj W hΔ
  exact ⟨integralCurveOver W⟩

/-- The bundled model has exactly the original integral cubic as its carrier. -/
theorem integralCurveGroup_carrier :
    (integralCurveGroup W hΔ).X = integralCurveOver W := rfl

end FLT.Mazur.WeierstrassIntegralChart
