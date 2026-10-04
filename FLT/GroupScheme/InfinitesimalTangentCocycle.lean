/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.SquareZeroPointDifference
public import FLT.GroupScheme.InfinitesimalConvolutionAddition

/-! # The actual discrepancy cocycle becomes addition of original tangents -/

@[expose] public noncomputable section
namespace HopfAlgebra
variable {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [HopfAlgebra R A] [Algebra R B] [Algebra R C]
  (q : B →ₐ[R] C) (hJ : RingHom.ker q ^ 2 = ⊥)

/-- Equal-reduction points give the additive tangent cocycle, without a chosen correction. -/
theorem pointDifferenceTangent_cocycle (f g h : A →ₐ[R] B)
    (hfg : q.comp f = q.comp g) (hgh : q.comp g = q.comp h) :
    pointDifferenceTangent q hJ f h (hfg.trans hgh) =
      pointDifferenceTangent q hJ f g hfg + pointDifferenceTangent q hJ g h hgh := by
  let fg : (Bialgebra.counitAlgHom R A).AugmentationPointKernel q :=
    ⟨pointDifference f g, pointDifference_reduction q f g hfg⟩
  let gh : (Bialgebra.counitAlgHom R A).AugmentationPointKernel q :=
    ⟨pointDifference g h, pointDifference_reduction q g h hgh⟩
  have hc : augmentationKernelConv q fg gh =
      ⟨pointDifference f h, pointDifference_reduction q f h (hfg.trans hgh)⟩ := by
    apply Subtype.ext
    exact pointDifference_cocycle f g h
  have ht := augmentationPointToTangent_conv q hJ fg gh
  rw [hc] at ht
  exact ht

/-- The cotangent functional of the discrepancy has the same additive cocycle identity. -/
theorem pointDifferenceCotangent_cocycle (f g h : A →ₐ[R] B)
    (hfg : q.comp f = q.comp g) (hgh : q.comp g = q.comp h) :
    (Bialgebra.counitAlgHom R A).augmentationTangentEquiv.symm
        (pointDifferenceTangent q hJ f h (hfg.trans hgh)) =
      (Bialgebra.counitAlgHom R A).augmentationTangentEquiv.symm
        (pointDifferenceTangent q hJ f g hfg) +
      (Bialgebra.counitAlgHom R A).augmentationTangentEquiv.symm
        (pointDifferenceTangent q hJ g h hgh) := by
  rw [pointDifferenceTangent_cocycle q hJ f g h hfg hgh, map_add]

end HopfAlgebra
