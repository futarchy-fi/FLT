/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.HopfFiberPointAction

/-!
# Points of the tensor-product fibre

The tensor-product coordinate fibre represents precisely the points mapping
to the chosen quotient point, over every test algebra.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct
open Algebra.TensorProduct WithConv
namespace HopfAlgebra

variable {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [HopfAlgebra R A] [HopfAlgebra R B] [Algebra R C]
  [Algebra B A] [IsScalarTower R B A]
  (f : B →ₐc[R] A) (hf : f.toAlgHom = IsScalarTower.toAlgHom R B A)
  (p : B →ₐ[R] R)

include hf in
/-- Restriction of the universal fibre point is the specified quotient point. -/
theorem pointFiberMap_comp :
    (pointFiberMap (A := A) p).comp f.toAlgHom =
      (Algebra.ofId R (PointFiber (A := A) p)).comp p := by
  let : Algebra B R := p.toRingHom.toAlgebra
  ext b
  change (1 : R) ⊗ₜ[B] f b = p b ⊗ₜ[B] (1 : A)
  have h := (TensorProduct.smul_tmul (R := B) b (1 : R) (1 : A)).symm
  change (1 : R) ⊗ₜ[B] f.toAlgHom b = _
  rw [hf]
  simpa [Algebra.smul_def, RingHom.algebraMap_toAlgebra] using h

/-- Restrict a point of the coordinate fibre to a point of the middle group. -/
def pointFiberRestrict (x : PointFiber (A := A) p →ₐ[R] C) :
    FiberPoints f (toConv ((Algebra.ofId R C).comp p)) :=
  ⟨toConv (x.comp (pointFiberMap p)), by
    apply ofConv_injective
    change (x.comp (pointFiberMap p)).comp f.toAlgHom = _
    rw [AlgHom.comp_assoc, pointFiberMap_comp f hf p]
    ext b
    exact x.commutes (p b)⟩

/-- A point above the specified quotient point descends to the coordinate fibre. -/
def pointFiberLift (x : FiberPoints f (toConv ((Algebra.ofId R C).comp p))) :
    PointFiber (A := A) p →ₐ[R] C := by
  let : Algebra B R := p.toRingHom.toAlgebra
  let : Algebra B C := ((Algebra.ofId R C).comp p).toRingHom.toAlgebra
  let : IsScalarTower B R C := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let xB : A →ₐ[B] C :=
    { toRingHom := x.val.ofConv.toRingHom
      commutes' b := by
        have h := congrArg (fun y : WithConv (B →ₐ[R] C) ↦ y.ofConv b) x.property
        change x.val.ofConv (f.toAlgHom b) = algebraMap B C b at h
        rw [hf] at h
        exact h }
  exact lift (Algebra.ofId R C) xB (fun _ _ ↦ .all ..)

/-- Restriction and descent are inverse on points over the quotient. -/
@[simp] theorem pointFiberRestrict_lift
    (x : FiberPoints f (toConv ((Algebra.ofId R C).comp p))) :
    pointFiberRestrict f hf p (pointFiberLift f hf p x) = x := by
  let : Algebra B R := p.toRingHom.toAlgebra
  let : Algebra B C := ((Algebra.ofId R C).comp p).toRingHom.toAlgebra
  let : IsScalarTower B R C := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  apply Subtype.ext
  apply ofConv_injective
  ext a
  change pointFiberLift f hf p x ((1 : R) ⊗ₜ[B] a) = x.val.ofConv a
  dsimp only [pointFiberLift]
  erw [lift_tmul]
  simp

/-- Restriction and descent are inverse on algebra maps from the fibre. -/
@[simp] theorem pointFiberLift_restrict (x : PointFiber (A := A) p →ₐ[R] C) :
    pointFiberLift f hf p (pointFiberRestrict f hf p x) = x := by
  let : Algebra B R := p.toRingHom.toAlgebra
  let : Algebra B C := ((Algebra.ofId R C).comp p).toRingHom.toAlgebra
  let : IsScalarTower B R C := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  apply Algebra.TensorProduct.ext
  · ext
  · ext a
    change pointFiberLift f hf p (pointFiberRestrict f hf p x) (1 ⊗ₜ[B] a) = _
    dsimp only [pointFiberLift]
    erw [lift_tmul]
    simp only [map_one, one_mul]
    rfl

/-- The coordinate fibre represents the actual quotient fibre functor. -/
def pointFiberPointsEquiv :
    (PointFiber (A := A) p →ₐ[R] C) ≃
      FiberPoints f (toConv ((Algebra.ofId R C).comp p)) where
  toFun := pointFiberRestrict f hf p
  invFun := pointFiberLift f hf p
  left_inv := pointFiberLift_restrict f hf p
  right_inv := pointFiberRestrict_lift f hf p

end HopfAlgebra
