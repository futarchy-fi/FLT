/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothGroupOperations
public import FLT.Mazur.WeierstrassSmoothAssociativity
public import FLT.Mazur.WeierstrassSmoothAdditionCommutative
public import FLT.Mazur.WeierstrassSmoothAdditionIdentity
public import FLT.Mazur.WeierstrassSmoothAdditionInverse
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_

/-!
# The smooth Weierstrass commutative group scheme

The entire relative smooth curve, with its constructed operations, is a
commutative group object over every coefficient spectrum, including bad reduction.
Every law comes from the established scheme morphism identities.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The global operations satisfy the monoid laws in the category over the base. -/
@[instance_reducible] def integralSmoothMonObj : MonObj (integralSmoothOver W) where
  one := integralSmoothOverZero W
  mul := integralSmoothOverAddition W
  one_mul := by
    apply (cancel_epi (λ_ (integralSmoothOver W)).inv).mp
    apply Over.OverMorphism.ext
    change (_ ≫ _) ≫ smoothFactorAddition W = _
    rw [integralSmoothOver_leftZero, smoothFactorAddition_left_identity]
    exact congrArg Over.Hom.left (Iso.inv_hom_id (λ_ (integralSmoothOver W))).symm
  mul_one := by
    apply (cancel_epi (ρ_ (integralSmoothOver W)).inv).mp
    apply Over.OverMorphism.ext
    change (_ ≫ _) ≫ smoothFactorAddition W = _
    rw [integralSmoothOver_rightZero, smoothFactorAddition_right_identity]
    exact congrArg Over.Hom.left (Iso.inv_hom_id (ρ_ (integralSmoothOver W))).symm
  mul_assoc := by
    apply Over.OverMorphism.ext
    change (integralSmoothOverAddition W ▷ integralSmoothOver W).left ≫
      smoothFactorAddition W = _
    rw [integralSmoothOver_addFirst]
    change _ = _ ≫ _ ≫ smoothFactorAddition W
    rw [← Category.assoc, integralSmoothOver_addLast]
    exact smoothFactorAddition_assoc W

/-- The constructed global negation supplies both inverse laws. -/
@[instance_reducible] def integralSmoothGrpObj : GrpObj (integralSmoothOver W) where
  __ := integralSmoothMonObj W
  inv := integralSmoothOverNegation W
  left_inv := by
    apply Over.OverMorphism.ext
    exact smoothFactorAddition_left_inverse W
  right_inv := by
    apply Over.OverMorphism.ext
    exact smoothFactorAddition_right_inverse W

/-- The regular addition is commutative as a group object. -/
@[instance_reducible] def integralSmoothCommGrpObj : CommGrpObj (integralSmoothOver W) where
  __ := integralSmoothGrpObj W
  mul_comm := by
    apply Over.OverMorphism.ext
    exact smoothFactorAddition_commutative W

/-- The bundled smooth commutative group scheme, with no assumed group laws. -/
def integralSmoothGroup : CommGrp (Over (Spec (.of R))) := by
  letI := integralSmoothCommGrpObj W
  exact ⟨integralSmoothOver W⟩

/-- The bundled model has exactly the original relative smooth curve as its carrier. -/
theorem integralSmoothGroup_carrier :
    (integralSmoothGroup W).X = integralSmoothOver W := rfl

end FLT.Mazur.WeierstrassIntegralChart
