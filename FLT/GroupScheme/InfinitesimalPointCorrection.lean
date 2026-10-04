/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.InfinitesimalTangentCocycle

/-! # Correcting actual local points by their infinitesimal discrepancy -/

@[expose] public noncomputable section
open WithConv
namespace HopfAlgebra
variable {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [HopfAlgebra R A] [Algebra R B] [Algebra R C]
  (q : B →ₐ[R] C) (hJ : RingHom.ker q ^ 2 = ⊥)

include hJ in
/-- For augmentation points, the group discrepancy is the difference of their tangents. -/
theorem augmentation_pointDifference_sub_counit
    (f g : (Bialgebra.counitAlgHom R A).AugmentationPointKernel q) (a : A) :
    pointDifference f.val g.val a - algebraMap R B (Bialgebra.counitAlgHom R A a) =
      g.val a - f.val a := by
  let d : (Bialgebra.counitAlgHom R A).AugmentationPointKernel q :=
    ⟨pointDifference f.val g.val, pointDifference_reduction q _ _
      (f.property.trans g.property.symm)⟩
  have hrec : augmentationKernelConv q f d = g := by
    apply Subtype.ext
    exact pointDifference_recover _ _
  have he := congrArg (fun t ↦ (t.val a : B)) (augmentationPointToTangent_conv q hJ f d)
  rw [hrec] at he
  change g.val a - algebraMap R B (Bialgebra.counitAlgHom R A a) =
    (f.val a - algebraMap R B (Bialgebra.counitAlgHom R A a)) +
    (pointDifference f.val g.val a - algebraMap R B (Bialgebra.counitAlgHom R A a)) at he
  linear_combination -he

variable [Coalgebra.IsCocomm R A]

/-- The original antipode makes cocommutative algebra-valued points a commutative group. -/
local instance correctionPointGroup : CommGroup (WithConv (A →ₐ[R] B)) where
  inv f := toConv (f.ofConv.comp (antipodeAlgHom R A))
  inv_mul_cancel f := conv_antipode_mul f.ofConv

/-- Equal discrepancies make the two corrected points agree. -/
theorem pointDifference_correction (f g c d : A →ₐ[R] B)
    (h : pointDifference f g = pointDifference c d) :
    (toConv f * toConv (c.comp (antipodeAlgHom R A))).ofConv =
      (toConv g * toConv (d.comp (antipodeAlgHom R A))).ofConv := by
  have he : (toConv f)⁻¹ * toConv g = (toConv c)⁻¹ * toConv d :=
    congrArg toConv h
  change (toConv f * (toConv c)⁻¹).ofConv = (toConv g * (toConv d)⁻¹).ofConv
  apply congrArg ofConv
  apply (mul_right_cancel_iff (a := toConv d)).mp
  calc
    _ = toConv f * ((toConv c)⁻¹ * toConv d) := by ac_rfl
    _ = toConv g := by rw [← he, mul_inv_cancel_left]
    _ = _ := by rw [mul_assoc, inv_mul_cancel, mul_one]

/-- Translate the first local point by the inverse correction on each side. -/
theorem pointDifference_corrected_eq (f g c d : A →ₐ[R] B)
    (h : pointDifference f g = pointDifference c d) :
    pointDifference c f = pointDifference d g := by
  change ((toConv c)⁻¹ * toConv f).ofConv = ((toConv d)⁻¹ * toConv g).ofConv
  rw [mul_comm ((toConv c)⁻¹), mul_comm ((toConv d)⁻¹)]
  exact pointDifference_correction f g c d h

/-- Translation by the augmentation leaves the original point unchanged. -/
theorem pointDifference_augmentation_left (f : A →ₐ[R] B) :
    pointDifference ((Algebra.ofId R B).comp (Bialgebra.counitAlgHom R A)) f = f := by
  change ((1 : WithConv (A →ₐ[R] B))⁻¹ * toConv f).ofConv = f
  rw [inv_one, one_mul]

end HopfAlgebra
