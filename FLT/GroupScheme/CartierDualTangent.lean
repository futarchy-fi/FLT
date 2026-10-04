/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.CartierDualMaps
public import FLT.Mathlib.RingTheory.AugmentationTangentEquiv
public import Mathlib.RingTheory.Bialgebra.Primitive

/-! # Tangent functionals are primitive elements of the actual integral Cartier dual -/

@[expose] public noncomputable section
open scoped TensorProduct
namespace HopfAlgebra.CartierDual
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [HopfAlgebra R A]
  [Module.Finite R A] [Module.Projective R A]

/-- The primitive condition on the actual dual is exactly Leibniz at the original counit. -/
theorem isPrimitive_iff_tangent (φ : CartierDual R A) :
    Bialgebra.IsPrimitiveElem R φ ↔
      ∀ a b : A, φ (a * b) = Coalgebra.counit (R := R) a * φ b +
        Coalgebra.counit (R := R) b * φ a := by
  rw [Bialgebra.isPrimitiveElem_iff_comul_eq_tmul_add_tmul]
  constructor
  · intro h a b
    have he := congrArg (fun z ↦ tensorEquiv R A A z (a ⊗ₜ b)) h
    change tensorEquiv R A A (comul φ) (a ⊗ₜ b) = _ at he
    simpa [mul_comm] using he
  · intro h
    apply tensor_ext R A A
    intro a b
    change tensorEquiv R A A (comul φ) (a ⊗ₜ b) = _
    simpa [mul_comm] using h a b

/-- Scalar-valued tangents identify with primitive elements through the original dual pairing. -/
def tangentPrimitiveEquiv :
    (Bialgebra.counitAlgHom R A).augmentationTangent (M := R) ≃ₗ[R]
      Coalgebra.skewPrimitive R (1 : CartierDual R A) 1 where
  toFun d := ⟨linearEquiv.symm d.val, (isPrimitive_iff_tangent _).mpr (by
    intro a b
    exact d.property a b)⟩
  invFun φ := ⟨linearEquiv φ.val, by
    intro a b
    exact (isPrimitive_iff_tangent φ.val).mp φ.property a b⟩
  left_inv d := by apply Subtype.ext; exact linearEquiv.apply_symm_apply _
  right_inv φ := by apply Subtype.ext; exact linearEquiv.symm_apply_apply _
  map_add' d e := by apply Subtype.ext; exact map_add linearEquiv.symm d.val e.val
  map_smul' r d := by apply Subtype.ext; exact map_smul linearEquiv.symm r d.val

/-- The primitive element evaluates by the original tangent functional. -/
theorem tangentPrimitiveEquiv_apply
    (d : (Bialgebra.counitAlgHom R A).augmentationTangent (M := R)) (a : A) :
    (tangentPrimitiveEquiv d).val a = d.val a := rfl

/-- The linear dual of the actual cotangent quotient is the primitive part of the Cartier dual. -/
def cotangentPrimitiveEquiv :
    Module.Dual R (RingHom.ker (Bialgebra.counitAlgHom R A)).Cotangent ≃ₗ[R]
      Coalgebra.skewPrimitive R (1 : CartierDual R A) 1 :=
  (AlgHom.augmentationTangentEquiv (Bialgebra.counitAlgHom R A)).trans tangentPrimitiveEquiv

/-- The tangent/dual identification retains evaluation on actual augmentation representatives. -/
theorem cotangentPrimitiveEquiv_apply
    (f : Module.Dual R (RingHom.ker (Bialgebra.counitAlgHom R A)).Cotangent) (a : A) :
    (cotangentPrimitiveEquiv f).val a =
      f ((Bialgebra.counitAlgHom R A).augmentationCotangent a) := rfl

end HopfAlgebra.CartierDual
