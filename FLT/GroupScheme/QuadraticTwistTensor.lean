/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.QuadraticTwistMaps

/-!
# Tensor products in quadratic descent

Scalar recovery is linear over the quadratic coefficient algebra. This lets
it be tensored over those coefficients, as required for comultiplication.
-/

@[expose] public section

open scoped TensorProduct QuadraticAlgebra

namespace QuadraticTwist

universe v
variable {R H : Type v} [CommRing R] [CommRing H] [Algebra R H]
variable (u : Rˣ) (ι : H ≃ₐ[R] H) (hι : Function.Involutive ι)
variable (r : R) (hr : 2 * r = 1)

/-- The coefficient map in scalar recovery is the usual left tensor inclusion. -/
theorem coefficientMap_eq_includeLeft :
    QuadraticDescent.coefficientMap (tensorUnit (H := H) u) (u : R) (tensorUnit_sq u) =
      (Algebra.TensorProduct.includeLeft : QuadraticAlgebra R (u : R) 0 →ₐ[R]
        QuadraticAlgebra R (u : R) 0 ⊗[R] H) := by
  apply QuadraticAlgebra.algHom_ext
  simp [QuadraticDescent.coefficientMap, QuadraticAlgebra.lift, tensorUnit, omegaUnit]

/-- Scalar recovery multiplies the coefficient by the fixed element. -/
@[simp] theorem scalarExtensionEquiv_tmul (s : QuadraticAlgebra R (u : R) 0)
    (a : model (u : R) ι) :
    scalarExtensionEquiv u ι hι r hr (s ⊗ₜ[R] a) =
      (s ⊗ₜ[R] (1 : H)) * a.val := by
  change QuadraticDescent.coefficientMap (tensorUnit u) (u : R) (tensorUnit_sq u) s * a.val = _
  rw [coefficientMap_eq_includeLeft]
  rfl

/-- Scalar recovery is an equivalence over the quadratic coefficients themselves. -/
noncomputable def scalarExtensionEquivOver :
    QuadraticAlgebra R (u : R) 0 ⊗[R] model (u : R) ι ≃ₐ[QuadraticAlgebra R (u : R) 0]
      QuadraticAlgebra R (u : R) 0 ⊗[R] H where
  __ := (scalarExtensionEquiv u ι hι r hr).toRingEquiv
  commutes' s := by
    change scalarExtensionEquiv u ι hι r hr (s ⊗ₜ[R] 1) = s ⊗ₜ[R] 1
    rw [scalarExtensionEquiv_tmul]
    exact mul_one _

/-- The real coefficient of a tensor over a quadratic algebra. -/
noncomputable def tensorRe (d : R) : QuadraticAlgebra R d 0 ⊗[R] H →ₗ[R] H :=
  (TensorProduct.lid R H).toLinearMap.comp
    (TensorProduct.map (QuadraticAlgebra.reₗ d 0) LinearMap.id)

/-- The imaginary coefficient of a tensor over a quadratic algebra. -/
noncomputable def tensorIm (d : R) : QuadraticAlgebra R d 0 ⊗[R] H →ₗ[R] H :=
  (TensorProduct.lid R H).toLinearMap.comp
    (TensorProduct.map (QuadraticAlgebra.imₗ d 0) LinearMap.id)

/-- Real coefficients on pure tensors. -/
@[simp] theorem tensorRe_tmul (d : R) (s : QuadraticAlgebra R d 0) (a : H) :
    tensorRe d (s ⊗ₜ[R] a) = s.re • a := rfl

/-- Imaginary coefficients on pure tensors. -/
@[simp] theorem tensorIm_tmul (d : R) (s : QuadraticAlgebra R d 0) (a : H) :
    tensorIm d (s ⊗ₜ[R] a) = s.im • a := rfl

/-- A tensor over a quadratic algebra is determined by its two coefficients. -/
theorem tensor_eq_re_add_im (d : R) (z : QuadraticAlgebra R d 0 ⊗[R] H) :
    z = 1 ⊗ₜ[R] tensorRe d z + QuadraticAlgebra.omega ⊗ₜ[R] tensorIm d z := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy =>
    simp only [map_add, TensorProduct.tmul_add]
    conv_lhs => rw [hx, hy]
    abel
  | tmul s a =>
    simpa only [TensorProduct.add_tmul, TensorProduct.smul_tmul, tensorRe_tmul,
      tensorIm_tmul] using congrArg (fun z : QuadraticAlgebra R d 0 ↦ z ⊗ₜ[R] a)
        (QuadraticAlgebra.re_smul_add_im_smul s).symm

include hr in
/-- Trivial twisting has no imaginary coefficient in its fixed elements. -/
theorem tensorIm_eq_zero_of_fixed (d : R)
    (z : model d (AlgEquiv.refl : H ≃ₐ[R] H)) : tensorIm d z.val = 0 := by
  have hi : tensorIm d (involution d (AlgEquiv.refl : H ≃ₐ[R] H) z.val) =
      -tensorIm d z.val := by
    induction z.val using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy, neg_add]
    | tmul s a =>
      change (star s).im • a = -(s.im • a)
      simp
  have hz : involution d (AlgEquiv.refl : H ≃ₐ[R] H) z.val = z.val := z.property
  rw [hz] at hi
  have htwo : (2 : R) • tensorIm d z.val = 0 := by
    rw [two_smul]
    exact add_eq_zero_iff_eq_neg.mpr hi
  calc
    tensorIm d z.val = (r * 2) • tensorIm d z.val := by rw [mul_comm r, hr, one_smul]
    _ = 0 := by rw [mul_smul, htwo, smul_zero]

/-- The fixed algebra of coefficient conjugation alone is the original algebra. -/
noncomputable def trivialModelEquiv (d : R) :
    model d (AlgEquiv.refl : H ≃ₐ[R] H) ≃ₐ[R] H := by
  let f : H →ₐ[R] model d (AlgEquiv.refl : H ≃ₐ[R] H) :=
    (Algebra.TensorProduct.includeRight : H →ₐ[R] QuadraticAlgebra R d 0 ⊗[R] H).codRestrict
      (model d AlgEquiv.refl) (fun a ↦ by
        change conjugation d 1 ⊗ₜ[R] a = 1 ⊗ₜ[R] a
        rw [map_one])
  refine (AlgEquiv.ofBijective f ⟨?_, ?_⟩).symm
  · intro a b h
    have h' := congrArg (fun z : model d (AlgEquiv.refl : H ≃ₐ[R] H) ↦ tensorRe d z.val) h
    simpa [f] using h'
  · intro z
    refine ⟨tensorRe d z.val, Subtype.ext ?_⟩
    change 1 ⊗ₜ[R] tensorRe d z.val = z.val
    have hz := tensor_eq_re_add_im d z.val
    rw [tensorIm_eq_zero_of_fixed r hr d z, TensorProduct.tmul_zero, add_zero] at hz
    exact hz.symm

end QuadraticTwist
