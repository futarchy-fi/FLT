/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudAugmentationRank
public import FLT.GroupScheme.RaynaudCartierDual

/-!
# The actual Cartier pairing on augmentation ideals

A dual augmentation functional vanishes on constants, so restriction to the
original augmentation ideal is an isomorphism. Its inverse extends a
functional by subtracting the constant counit component.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]

/-- Subtract the counit component to project onto the augmentation ideal. -/
def FF.augmentationProjection (X : FF R K) : X.CoordinateRing →ₗ[R] X.augmentation :=
  (LinearMap.snd R R X.augmentation).comp X.augmentationSplit.toLinearMap

/-- The augmentation projection subtracts exactly the constant component. -/
@[simp] theorem FF.augmentationProjection_apply (X : FF R K) (a : X.CoordinateRing) :
    (X.augmentationProjection a : X.CoordinateRing) =
      a - algebraMap R X.CoordinateRing (Coalgebra.counit a) := rfl

/-- Projection is the identity on the actual augmentation ideal. -/
@[simp] theorem FF.augmentationProjection_coe (X : FF R K) (a : X.augmentation) :
    X.augmentationProjection a = a := by
  apply Subtype.ext
  rw [X.augmentationProjection_apply, a.property, map_zero, sub_zero]

variable [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K] [CharZero K]

/-- Restriction of the actual Cartier pairing is perfect on the augmentation ideals. -/
def FF.augmentationDuality (X : FF R K) :
    X.cartierDual.augmentation ≃ₗ[R] Module.Dual R X.augmentation where
  toFun φ := (HopfAlgebra.CartierDual.linearEquiv φ.val).comp X.augmentation.subtype
  invFun f := ⟨WithConv.toConv (f.comp X.augmentationProjection), by
    change f (X.augmentationProjection 1) = 0
    have h : X.augmentationProjection 1 = 0 := by
      apply Subtype.ext
      simp
    rw [h, map_zero]⟩
  left_inv φ := by
    apply Subtype.ext
    apply WithConv.ext
    ext a
    let f : Module.Dual R X.CoordinateRing := HopfAlgebra.CartierDual.linearEquiv φ.val
    have hφ : f 1 = 0 := φ.property
    change f (a - algebraMap R X.CoordinateRing (Coalgebra.counit a)) = f a
    rw [map_sub, Algebra.algebraMap_eq_smul_one, map_smul, hφ, smul_zero, sub_zero]
  right_inv f := by
    ext a
    change f (X.augmentationProjection a) = f a
    rw [X.augmentationProjection_coe]
  map_add' f g := by ext a; rfl
  map_smul' r f := by ext a; rfl

/-- The restricted perfect pairing is evaluation of the original dual coordinate. -/
@[simp] theorem FF.augmentationDuality_apply (X : FF R K)
    (φ : X.cartierDual.augmentation) (a : X.augmentation) :
    X.augmentationDuality φ a =
      (show HopfAlgebra.CartierDual R X.CoordinateRing from φ.val) a := rfl

end ThreeAdicPlan
