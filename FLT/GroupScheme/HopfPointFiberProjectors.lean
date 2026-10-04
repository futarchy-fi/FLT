/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.HopfPointFiberCoactionLaws
public import FLT.GroupScheme.HopfPointFiberHomogeneous

/-!
# Coefficient projectors on the actual Hopf fibre

The kernel basis is input; the projectors, orthogonality, and decomposition
are derived from the constructed fibre coaction and Hopf structural laws.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace HopfAlgebra

variable {R A B G : Type*} [CommRing R] [CommRing A] [CommRing B]
  [HopfAlgebra R A] [HopfAlgebra R B] [Algebra B A] [IsScalarTower R B A]
  (f : B →ₐc[R] A) (hf : f.toAlgHom = IsScalarTower.toAlgHom R B A)
  (p : B →ₐ[R] R) (b : Module.Basis G R (A ⧸ augmentationIdeal f))

/-- A coefficient of the actual coaction, with no supplied projector family. -/
def pointFiberProjector (i : G) : PointFiber (A := A) p →ₗ[R] PointFiber (A := A) p :=
  CoactionBasis.projector b (pointFiberCoaction f hf p).toLinearMap i

variable
  (hδ : CoactionBasis.diagonal b ∘ₗ (Ideal.Quotient.mkₐ R (augmentationIdeal f)).toLinearMap =
    TensorProduct.map (Ideal.Quotient.mkₐ R (augmentationIdeal f)).toLinearMap
      (Ideal.Quotient.mkₐ R (augmentationIdeal f)).toLinearMap ∘ₗ Coalgebra.comul)

include hδ in
/-- Each extracted coefficient lies in the actual homogeneous submodule. -/
theorem pointFiberProjector_mem (i : G) (x : PointFiber (A := A) p) :
    pointFiberProjector f hf p b i x ∈ pointFiberHomogeneous f hf p (b i) :=
  CoactionBasis.projector_homogeneous b (pointFiberCoaction f hf p).toLinearMap
    (pointFiberCoaction_coassoc f hf p b hδ) i x

include hδ in
open Classical in
/-- The extracted projectors are orthogonal and idempotent. -/
theorem pointFiberProjector_projector (i j : G) (x : PointFiber (A := A) p) :
    pointFiberProjector f hf p b i (pointFiberProjector f hf p b j x) =
      if j = i then pointFiberProjector f hf p b j x else 0 :=
  CoactionBasis.projector_projector b (pointFiberCoaction f hf p).toLinearMap
    (pointFiberCoaction_coassoc f hf p b hδ) i j x

variable [Fintype G]

/-- The coaction is the finite sum of its degree coefficients. -/
theorem pointFiberCoaction_decomposition (x : PointFiber (A := A) p) :
    ∑ i, pointFiberProjector f hf p b i x ⊗ₜ[R] b i = pointFiberCoaction f hf p x :=
  CoactionBasis.sum_coefficient b (pointFiberCoaction f hf p x)

/-- Compatibility with the actual Hopf counit makes the projector sum the identity. -/
theorem pointFiberProjector_sum
    (hε : CoactionBasis.augmentation b ∘ₗ
      (Ideal.Quotient.mkₐ R (augmentationIdeal f)).toLinearMap = Coalgebra.counit)
    (x : PointFiber (A := A) p) : ∑ i, pointFiberProjector f hf p b i x = x := by
  apply CoactionBasis.sum_projector b (pointFiberCoaction f hf p).toLinearMap
  intro y
  have he : (TensorProduct.rid R (PointFiber (A := A) p)).toLinearMap ∘ₗ
      (CoactionBasis.augmentation b).lTensor (PointFiber (A := A) p) ∘ₗ
      (pointFiberCoaction f hf p).toLinearMap = LinearMap.id := by
    apply pointFiber_linear_ext p
    intro a
    exact Coalgebra.coaction_counit_on_image (pointFiberMap (A := A) p).toLinearMap
      (Ideal.Quotient.mkₐ R (augmentationIdeal f)).toLinearMap
      (pointFiberCoaction f hf p).toLinearMap (pointFiberCoaction_linear_comp f hf p)
      (CoactionBasis.augmentation b) hε a
  exact LinearMap.congr_fun he y

end HopfAlgebra
