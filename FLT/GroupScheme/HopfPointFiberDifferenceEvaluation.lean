/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.HopfPointFiberHomogeneous

/-!
# Evaluation of the constructed fibre difference

The inverse of the canonical torsor comparison constructs the kernel point
between any two fibre points. A homogeneous unit evaluates to their root ratio.
No evaluation identity or comparison isomorphism is an input.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct
open Algebra.TensorProduct
open WithConv
namespace HopfAlgebra

variable {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [HopfAlgebra R A] [HopfAlgebra R B] [Algebra B A] [IsScalarTower R B A]
  [Algebra R C]
  (f : B →ₐc[R] A) (hf : f.toAlgHom = IsScalarTower.toAlgHom R B A)
  (p : B →ₐ[R] R)
  (x y : PointFiber (A := A) p →ₐ[R] C)

/-- The kernel point obtained from the actual inverse torsor comparison. -/
def pointFiberDifferenceEvaluation : (A ⧸ augmentationIdeal f) →ₐ[R] C :=
  ((lift x y (fun _ _ ↦ .all ..)).comp
    ((pointFiberTorsorEquiv f hf p).symm.restrictScalars R).toAlgHom).comp includeRight

set_option maxRecDepth 2048 in
/-- Evaluating a coaction at the first point and the difference gives the second point. -/
theorem pointFiberDifferenceEvaluation_coaction (z : PointFiber (A := A) p) :
    lift x (pointFiberDifferenceEvaluation f hf p x y) (fun _ _ ↦ .all ..)
      (pointFiberCoaction f hf p z) = y z := by
  have he : lift x (pointFiberDifferenceEvaluation f hf p x y) (fun _ _ ↦ .all ..) =
      (lift x y (fun _ _ ↦ .all ..)).comp
        ((pointFiberTorsorEquiv f hf p).symm.restrictScalars R).toAlgHom := by
    apply Algebra.TensorProduct.ext
    · ext a
      simp only [AlgHom.comp_apply, includeLeft_apply, lift_tmul, map_one, mul_one]
      change x a = lift x y (fun _ _ ↦ .all ..)
        ((pointFiberTorsorEquiv f hf p).symm (algebraMap (PointFiber (A := A) p) _ a))
      rw [AlgEquiv.commutes]
      simp
    · ext b
      simp [pointFiberDifferenceEvaluation]
  rw [he]
  change lift x y (fun _ _ ↦ .all ..)
    ((pointFiberTorsorEquiv f hf p).symm
      (pointFiberTorsorEquiv f hf p (1 ⊗ₜ[R] z))) = _
  simp

/-- On middle coordinates this is the Hopf point difference, with its actual
antipode and convolution law. -/
theorem pointFiberDifferenceEvaluation_map :
    (pointFiberDifferenceEvaluation f hf p x y).comp
      (Ideal.Quotient.mkₐ R (augmentationIdeal f)) =
    (toConv ((x.comp (pointFiberMap p)).comp (antipodeAlgHom R A)) *
      toConv (y.comp (pointFiberMap p))).ofConv := by
  let d := (pointFiberDifferenceEvaluation f hf p x y).comp
    (Ideal.Quotient.mkₐ R (augmentationIdeal f))
  let u := x.comp (pointFiberMap (A := A) p)
  let v := y.comp (pointFiberMap (A := A) p)
  have huv : toConv u * toConv d = toConv v := by
    apply ofConv_injective
    ext a
    have h := pointFiberDifferenceEvaluation_coaction f hf p x y (pointFiberMap p a)
    rw [pointFiberCoaction_map] at h
    have hm : (lift x (pointFiberDifferenceEvaluation f hf p x y)
        (fun _ _ ↦ .all ..)).comp
        (Algebra.TensorProduct.map (pointFiberMap (A := A) p)
          (AlgHom.id R (A ⧸ augmentationIdeal f))) =
        lift u (pointFiberDifferenceEvaluation f hf p x y) (fun _ _ ↦ .all ..) := by
      ext <;> simp [u]
    change ((lift x (pointFiberDifferenceEvaluation f hf p x y)
      (fun _ _ ↦ .all ..)).comp
      (Algebra.TensorProduct.map (pointFiberMap p) (AlgHom.id R _)))
      (torsorCoaction f a) = _ at h
    rw [hm, torsorCoaction_eq_conv] at h
    have he := AlgHom.comp_convMul_distrib
      (lift u (pointFiberDifferenceEvaluation f hf p x y) (fun _ _ ↦ .all ..))
      (toConv (includeLeft : A →ₐ[R] A ⊗[R] (A ⧸ augmentationIdeal f)))
      (toConv (includeRight.comp (Ideal.Quotient.mkₐ R (augmentationIdeal f))))
    have he' := AlgHom.congr_fun he a
    have hd : (lift u (pointFiberDifferenceEvaluation f hf p x y) (fun _ _ ↦ .all ..)).comp
        (includeRight.comp (Ideal.Quotient.mkₐ R (augmentationIdeal f))) = d := by
      ext b
      simp [d]
    rw [hd] at he'
    simpa [u, v, d] using he'.symm.trans h
  have hc := congrArg (toConv (u.comp (antipodeAlgHom R A)) * ·) huv
  rw [← mul_assoc, conv_antipode_mul, one_mul] at hc
  exact congrArg ofConv hc

/-- Homogeneous coordinates transform by evaluation of the actual difference. -/
theorem pointFiberDifferenceEvaluation_mul (z : PointFiber (A := A) p)
    (t : A ⧸ augmentationIdeal f) (hz : z ∈ pointFiberHomogeneous f hf p t) :
    y z = x z * pointFiberDifferenceEvaluation f hf p x y t := by
  have h := pointFiberDifferenceEvaluation_coaction f hf p x y z
  rw [mem_pointFiberHomogeneous] at hz
  rw [hz, lift_tmul] at h
  exact h.symm

/-- In unit coordinates the constructed difference is exactly the root ratio. -/
theorem pointFiberDifferenceEvaluation_unitRatio
    (z : (PointFiber (A := A) p)ˣ) (t : (A ⧸ augmentationIdeal f)ˣ)
    (hz : (z : PointFiber (A := A) p) ∈ pointFiberHomogeneous f hf p t) :
    Units.map (pointFiberDifferenceEvaluation f hf p x y).toMonoidHom t =
      Units.map y.toMonoidHom z / Units.map x.toMonoidHom z := by
  apply (eq_div_iff_mul_eq').mpr
  apply Units.ext
  change pointFiberDifferenceEvaluation f hf p x y t * x z = y z
  simpa only [mul_comm] using
    (pointFiberDifferenceEvaluation_mul f hf p x y z t hz).symm

/-- Evaluation at a Galois translate yields the usual Galois root ratio. -/
theorem pointFiberDifferenceEvaluation_galoisRatio
    (σ : C ≃ₐ[R] C) (z : (PointFiber (A := A) p)ˣ)
    (t : (A ⧸ augmentationIdeal f)ˣ)
    (hz : (z : PointFiber (A := A) p) ∈ pointFiberHomogeneous f hf p t) :
    Units.map (pointFiberDifferenceEvaluation f hf p x (σ.toAlgHom.comp x)).toMonoidHom t =
      Units.map σ.toMonoidHom (Units.map x.toMonoidHom z) / Units.map x.toMonoidHom z :=
  pointFiberDifferenceEvaluation_unitRatio f hf p x (σ.toAlgHom.comp x) z t hz

end HopfAlgebra
