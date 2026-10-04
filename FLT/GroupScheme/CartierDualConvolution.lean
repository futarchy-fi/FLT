/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.CartierDualMaps

/-! # Transposition preserves convolution and reverses composition -/

@[expose] public noncomputable section
open scoped TensorProduct
open WithConv
namespace HopfAlgebra.CartierDual
variable {R A B C : Type} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [HopfAlgebra R A] [HopfAlgebra R B] [HopfAlgebra R C]
  [Module.Finite R A] [Module.Projective R A]
  [Module.Finite R B] [Module.Projective R B]
  [Module.Finite R C] [Module.Projective R C]

/-- Transposing a composite reverses its order. -/
@[simp] theorem bialgMap_comp (f : A →ₐc[R] B) (g : B →ₐc[R] C) :
    bialgMap (g.comp f) = (bialgMap f).comp (bialgMap g) := by
  ext φ a
  rfl

variable [Coalgebra.IsCocomm R A] [Coalgebra.IsCocomm R B]

omit [Coalgebra.IsCocomm R B] in
/-- Transposition preserves the convolution unit. -/
@[simp] theorem bialgMap_convOne :
    bialgMap (1 : WithConv (A →ₐc[R] B)).ofConv =
      (1 : WithConv (CartierDual R B →ₐc[R] CartierDual R A)).ofConv := by
  ext φ a
  change φ (algebraMap R B (Coalgebra.counit a)) = φ 1 * Coalgebra.counit a
  simp [Algebra.algebraMap_eq_smul_one, mul_comm]

omit [Coalgebra.IsCocomm R A] [Coalgebra.IsCocomm R B] in
private theorem transpose_mul_eval (f g : A →ₐc[R] B)
    (t : CartierDual R B ⊗[R] CartierDual R B) (a : A) :
    (LinearMap.mul' R (CartierDual R A)
      (TensorProduct.map (bialgMap f).toLinearMap (bialgMap g).toLinearMap t)) a =
        tensorEquiv R B B t
          (TensorProduct.map f.toLinearMap g.toLinearMap (Coalgebra.comul a)) := by
  induction t using TensorProduct.inductionOn with
  | tmul φ ψ =>
    simp only [TensorProduct.map_tmul, LinearMap.mul'_apply]
    rw [LinearMap.convMul_apply]
    generalize Coalgebra.comul (R := R) a = s
    induction s using TensorProduct.inductionOn with
    | tmul x y =>
      simp only [TensorProduct.map_tmul, LinearMap.mul'_apply, tensorEquiv_tmul]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  | add x y hx hy => simp only [map_add, WithConv.ofConv_add, LinearMap.add_apply, hx, hy]

omit [Coalgebra.IsCocomm R B] in
/-- The transpose of a sum of group morphisms is the sum of their transposes. -/
theorem bialgMap_convMul (f g : A →ₐc[R] B) :
    bialgMap (toConv f * toConv g).ofConv =
      (toConv (bialgMap f) * toConv (bialgMap g)).ofConv := by
  ext φ a
  change φ ((toConv f.toAlgHom * toConv g.toAlgHom).ofConv a) =
    (LinearMap.mul' R (CartierDual R A)
      (TensorProduct.map (bialgMap f).toLinearMap (bialgMap g).toLinearMap (comul φ))) a
  rw [transpose_mul_eval, AlgHom.convMul_apply]
  generalize Coalgebra.comul (R := R) a = s
  induction s using TensorProduct.inductionOn with
  | tmul x y =>
    simp only [TensorProduct.map_tmul, comul_eval]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

omit [Coalgebra.IsCocomm R B] in
/-- Transposition preserves every natural convolution power. -/
theorem bialgMap_convPow (f : A →ₐc[R] B) (n : ℕ) :
    bialgMap (toConv f ^ n).ofConv = (toConv (bialgMap f) ^ n).ofConv := by
  induction n with
  | zero => simp
  | succ n hn =>
    simpa only [pow_succ, ← bialgMap_convMul, toConv_ofConv, hn]
      using bialgMap_convMul (toConv f ^ n).ofConv f

end HopfAlgebra.CartierDual
