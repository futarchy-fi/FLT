/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.HopfAlgebra.Convolution

/-! # The group of Hopf points in an arbitrary commutative test algebra -/

@[expose] public noncomputable section
open Algebra.TensorProduct WithConv
namespace HopfAlgebra
variable (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
  [HopfAlgebra R A] [Algebra R B]

/-- Convolution and the antipode give a group without any coalgebra structure
on the test algebra. -/
@[instance_reducible]
def testAlgebraPointGroup : Group (WithConv (A →ₐ[R] B)) where
  toMonoid := inferInstance
  inv f := toConv (f.ofConv.comp (antipodeAlgHom R A))
  inv_mul_cancel f := by
    have H : (lmul' R).comp (Algebra.TensorProduct.map f.ofConv f.ofConv) =
        f.ofConv.comp (lmul' R) := by ext <;> simp
    trans toConv (((lmul' R).comp (Algebra.TensorProduct.map f.ofConv f.ofConv)).comp
      ((Algebra.TensorProduct.map (antipodeAlgHom R A) (.id _ _)).comp
        (Bialgebra.comulAlgHom R A)))
    · rw [AlgHom.comp_assoc, ← AlgHom.comp_assoc (Algebra.TensorProduct.map f.ofConv f.ofConv),
        ← Algebra.TensorProduct.map_comp]
      rfl
    rw [H, AlgHom.comp_assoc, WithConv.ext_iff, ← AlgHom.toLinearMap_injective.eq_iff]
    change f.ofConv.toLinearMap.comp (toConv (antipode R (A := A)) * toConv LinearMap.id).ofConv =
      ofConv (1 : WithConv (A →ₗ[R] B))
    rw [LinearMap.antipode_mul_id]
    ext
    simp
end HopfAlgebra
