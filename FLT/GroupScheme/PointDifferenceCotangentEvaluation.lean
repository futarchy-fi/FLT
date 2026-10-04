/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.SquareZeroPointDifference

/-! # Cotangent discrepancies retain their original coordinate values -/

@[expose] public noncomputable section
namespace AlgHom
variable {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra R C]
  (ε : A →ₐ[R] R) (q : B →ₐ[R] C) (hJ : RingHom.ker q ^ 2 = ⊥)

/-- Evaluation on the augmentation projection recovers the original point minus its counit. -/
theorem augmentationPointCotangentEquiv_projection (f : ε.AugmentationPointKernel q) (a : A) :
    (ε.augmentationPointCotangentEquiv q hJ f (ε.augmentationCotangent a) : B) =
      f.val a - algebraMap R B (ε a) := by
  have he := congrArg (fun t : ε.augmentationTangent (M := RingHom.ker q) ↦ (t.val a : B))
    (ε.augmentationTangentEquiv.apply_symm_apply (ε.augmentationPointToTangent q hJ f))
  exact he

end AlgHom
namespace HopfAlgebra
variable {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [HopfAlgebra R A] [Algebra R B] [Algebra R C]

/-- The discrepancy of actual points commutes with the specified map of coefficient rings. -/
theorem pointDifference_postcomp (β : B →ₐ[R] C) (f g : A →ₐ[R] B) :
    β.comp (pointDifference f g) = pointDifference (β.comp f) (β.comp g) := by
  simp only [pointDifference, AlgHom.comp_convMul_distrib, AlgHom.comp_assoc]

end HopfAlgebra
