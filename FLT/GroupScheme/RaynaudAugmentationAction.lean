/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudScalarAction
public import Mathlib.RepresentationTheory.Invariants

/-!
# Scalar units acting on the augmentation ideal

The scalar maps supplied by the extremal-model construction preserve the
actual counit kernel. Their contravariant composition law defines a
representation because the scalar ring is commutative.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan

variable {R K F : Type} [CommRing R] [Field K] [Algebra R K] [CommSemiring F]
  (X : FF R K)

/-- The augmentation submodule of the actual coordinate Hopf algebra. -/
def FF.augmentation : Submodule R X.CoordinateRing :=
  LinearMap.ker (Coalgebra.counit (R := R))

/-- Every model endomorphism preserves the augmentation submodule. -/
theorem ModelHom.maps_augmentation (f : ModelHom X X) :
    X.augmentation ≤ X.augmentation.comap f.toLinearMap := by
  intro x hx
  change Coalgebra.counit (f x) = 0
  rw [CoalgHomClass.counit_comp_apply]
  exact hx

/-- Scalar units act on coordinates, with the order reversal removed by commutativity. -/
def FF.scalarRepresentation (lift : F → ModelHom X X)
    (h1 : lift 1 = BialgHom.id R X.CoordinateRing)
    (hmul : ∀ a b, lift (a * b) = (lift b).comp (lift a)) :
    Representation R Fˣ X.CoordinateRing where
  toFun a := (lift a).toLinearMap
  map_one' := by ext x; change lift 1 x = x; rw [h1]; rfl
  map_mul' a b := by
    ext x
    change lift (↑a * ↑b) x = lift a (lift b x)
    rw [mul_comm (a : F), hmul]
    rfl

/-- Restriction of the scalar representation to the actual augmentation ideal. -/
def FF.augmentationRepresentation (lift : F → ModelHom X X)
    (h1 : lift 1 = BialgHom.id R X.CoordinateRing)
    (hmul : ∀ a b, lift (a * b) = (lift b).comp (lift a)) :
    Representation R Fˣ X.augmentation :=
  (X.scalarRepresentation lift h1 hmul).subrepresentation X.augmentation
    fun a ↦ ModelHom.maps_augmentation X (lift a)

/-- The restricted action is the original scalar map on underlying coordinates. -/
@[simp] theorem FF.augmentationRepresentation_apply (lift : F → ModelHom X X)
    (h1 : lift 1 = BialgHom.id R X.CoordinateRing)
    (hmul : ∀ a b, lift (a * b) = (lift b).comp (lift a))
    (a : Fˣ) (x : X.augmentation) :
    ((X.augmentationRepresentation lift h1 hmul a x : X.augmentation) : X.CoordinateRing) =
      lift a x := rfl

end ThreeAdicPlan
