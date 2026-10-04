/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.AugmentationTangent
public import Mathlib.RingTheory.Bialgebra.Convolution

/-! # The augmentation differential of convolution -/

@[expose] public noncomputable section
open scoped TensorProduct
open WithConv
namespace AlgHom
variable {R A B M : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Bialgebra R A] [Bialgebra R B] [AddCommGroup M] [Module R M]

/-- Leibniz and the two counit identities turn convolution into addition of derivatives. -/
theorem augmentationTangent_convolution
    (d : (Bialgebra.counitAlgHom R B).augmentationTangent (M := M))
    (f g : A →ₐc[R] B) (a : A) :
    d.val ((toConv f.toAlgHom * toConv g.toAlgHom) a) = d.val (f a) + d.val (g a) := by
  let L := Algebra.TensorProduct.lift f.toAlgHom g.toAlgHom (fun _ _ ↦ .all _ _)
  have he : d.val.comp L.toLinearMap =
      (d.val.comp g.toAlgHom.toLinearMap).comp
        ((TensorProduct.lid R A).toLinearMap.comp ((Coalgebra.counit (R := R)).rTensor A)) +
      (d.val.comp f.toAlgHom.toLinearMap).comp
        ((TensorProduct.rid R A).toLinearMap.comp ((Coalgebra.counit (R := R)).lTensor A)) := by
    ext x y
    change d.val (f x * g y) = _
    rw [d.property]
    simp only [Bialgebra.counitAlgHom_apply, CoalgHomClass.counit_comp_apply]
    simp [LinearMap.comp_apply]
  rw [convMul_apply]
  change (d.val.comp L.toLinearMap) (Coalgebra.comul a) = _
  rw [he]
  simp [LinearMap.comp_apply, add_comm]

end AlgHom
