/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.InfinitesimalConvolutionAddition

/-! # The cotangent functional of a square-zero group product -/

@[expose] public noncomputable section
namespace HopfAlgebra
variable {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Bialgebra R A] [Algebra R B] [Algebra R C]
  (q : B →ₐ[R] C) (hJ : RingHom.ker q ^ 2 = ⊥)

/-- Cotangent extraction takes the original convolution to addition of functionals. -/
theorem augmentationPointCotangentEquiv_conv
    (f g : (Bialgebra.counitAlgHom R A).AugmentationPointKernel q) :
    AlgHom.augmentationPointCotangentEquiv _ q hJ (augmentationKernelConv q f g) =
      AlgHom.augmentationPointCotangentEquiv _ q hJ f +
        AlgHom.augmentationPointCotangentEquiv _ q hJ g := by
  change (Bialgebra.counitAlgHom R A).augmentationTangentEquiv.symm
    (AlgHom.augmentationPointToTangent _ q hJ (augmentationKernelConv q f g)) = _
  rw [augmentationPointToTangent_conv, map_add]
  rfl

end HopfAlgebra
