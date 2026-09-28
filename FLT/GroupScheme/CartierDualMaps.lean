/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.CartierDualHopf

/-!
# Integral Cartier duality on morphisms

The transpose of an integral Hopf map respects the dual coalgebra as well as
the convolution algebra. Evaluation identifies each finite projective Hopf
algebra with its double dual.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace HopfAlgebra.CartierDual

universe u

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [HopfAlgebra R A] [HopfAlgebra R B]
  [Module.Finite R A] [Module.Projective R A] [Coalgebra.IsCocomm R A]
  [Module.Finite R B] [Module.Projective R B] [Coalgebra.IsCocomm R B]

/-- Evaluation of a tensor of dual maps is precomposition on both factors. -/
theorem tensor_map_eval (f : A →ₐc[R] B)
    (t : CartierDual R B ⊗[R] CartierDual R B) (a b : A) :
    tensorEquiv R A A (TensorProduct.map (map f).toLinearMap (map f).toLinearMap t)
      (a ⊗ₜ b) = tensorEquiv R B B t (f a ⊗ₜ f b) := by
  induction t using TensorProduct.inductionOn with
  | tmul φ ψ => simp
  | add x y hx hy => simp [hx, hy]

/-- The transpose of an integral Hopf map is an integral Hopf map. -/
def bialgMap (f : A →ₐc[R] B) : CartierDual R B →ₐc[R] CartierDual R A where
  __ := map f
  map_smul' := map_smul (map f)
  counit_comp := by
    ext φ
    change map f φ 1 = φ 1
    simp
  map_comp_comul := by
    ext φ : 1
    apply tensor_ext R A A
    intro a b
    change tensorEquiv R A A
      (TensorProduct.map (map f).toLinearMap (map f).toLinearMap (comul φ)) (a ⊗ₜ b) =
        tensorEquiv R A A (comul (map f φ)) (a ⊗ₜ b)
    simp [tensor_map_eval]

/-- The dual Hopf map evaluates by precomposition. -/
@[simp] theorem bialgMap_apply (f : A →ₐc[R] B) (φ : CartierDual R B) (a : A) :
    bialgMap f φ a = φ (f a) := rfl

/-- Integral duality preserves identity maps. -/
@[simp] theorem bialgMap_id : bialgMap (BialgHom.id R A) = BialgHom.id R (CartierDual R A) := by
  ext φ a
  rfl

/-- Evaluation identifies the underlying module with its double integral dual. -/
def bidualLinearEquiv : A ≃ₗ[R] CartierDual R (CartierDual R A) :=
  (Module.evalEquiv R A).trans
    ((linearEquiv (R := R) (A := A)).dualMap.trans linearEquiv.symm)

/-- The double dual comparison is the usual evaluation pairing. -/
@[simp] theorem bidualLinearEquiv_apply (a : A) (φ : CartierDual R A) :
    bidualLinearEquiv a φ = φ a := rfl

private theorem bidual_mul_eval (a b : A)
    (t : CartierDual R A ⊗[R] CartierDual R A) :
    LinearMap.mul' R R
      (TensorProduct.map (bidualLinearEquiv a).ofConv (bidualLinearEquiv b).ofConv t) =
        tensorEquiv R A A t (a ⊗ₜ b) := by
  induction t using TensorProduct.inductionOn with
  | tmul φ ψ => simp
  | add x y hx hy => simp [hx, hy]

/-- Evaluation is an algebra equivalence with the integral double dual. -/
def bidualAlgEquiv : A ≃ₐ[R] CartierDual R (CartierDual R A) :=
  { bidualLinearEquiv with
    map_mul' := by
      intro a b
      apply WithConv.ext
      ext φ
      change φ (a * b) = LinearMap.mul' R R
        (TensorProduct.map (bidualLinearEquiv a).ofConv (bidualLinearEquiv b).ofConv (comul φ))
      rw [bidual_mul_eval, comul_eval]
    commutes' := by
      intro r
      apply WithConv.ext
      ext φ
      change φ (algebraMap R A r) = r * φ 1
      simp [Algebra.algebraMap_eq_smul_one] }

/-- The double dual algebra equivalence evaluates functionals. -/
@[simp] theorem bidualAlgEquiv_apply (a : A) (φ : CartierDual R A) :
    bidualAlgEquiv a φ = φ a := rfl

private theorem tensor_bidual_eval (t : A ⊗[R] A) (φ ψ : CartierDual R A) :
    tensorEquiv R (CartierDual R A) (CartierDual R A)
      (TensorProduct.map bidualAlgEquiv.toLinearMap bidualAlgEquiv.toLinearMap t) (φ ⊗ₜ ψ) =
        LinearMap.mul' R R (TensorProduct.map φ.ofConv ψ.ofConv t) := by
  induction t using TensorProduct.inductionOn with
  | tmul a b => simp
  | add x y hx hy => simp [hx, hy]

/-- Evaluation is an integral Hopf algebra equivalence with the double dual. -/
def bidualEquiv : A ≃ₐc[R] CartierDual R (CartierDual R A) :=
  BialgEquiv.ofAlgEquiv bidualAlgEquiv
    (by
      ext a
      change (1 : CartierDual R A) a = Coalgebra.counit (R := R) a
      simp)
    (by
      ext a : 1
      apply tensor_ext R (CartierDual R A) (CartierDual R A)
      intro φ ψ
      change tensorEquiv R (CartierDual R A) (CartierDual R A)
        (TensorProduct.map bidualAlgEquiv.toLinearMap bidualAlgEquiv.toLinearMap
          (Coalgebra.comul a)) (φ ⊗ₜ ψ) =
            tensorEquiv R (CartierDual R A) (CartierDual R A)
              (comul (bidualAlgEquiv a)) (φ ⊗ₜ ψ)
      rw [tensor_bidual_eval, comul_eval]
      rfl)

/-- Double duality evaluates by the original pairing. -/
@[simp] theorem bidualEquiv_apply (a : A) (φ : CartierDual R A) :
    bidualEquiv a φ = φ a := rfl

end HopfAlgebra.CartierDual
