/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.CoactionBasisProjectors
public import FLT.GroupScheme.CoactionDescentLaws
public import FLT.GroupScheme.HopfPointFiberTorsor

/-!
# Coassociativity of the actual fibre coaction

The diagonal kernel law is checked on the quotient map out of the middle Hopf
algebra. Hopf coassociativity then supplies the fibre coaction law.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct
namespace HopfAlgebra

variable {R A B G : Type*} [CommRing R] [CommRing A] [CommRing B]
  [HopfAlgebra R A] [HopfAlgebra R B] [Algebra B A] [IsScalarTower R B A]
  (f : B →ₐc[R] A) (hf : f.toAlgHom = IsScalarTower.toAlgHom R B A)
  (p : B →ₐ[R] R) (b : Module.Basis G R (A ⧸ augmentationIdeal f))


/-- The fibre coaction is induced by the actual middle comultiplication. -/
theorem pointFiberCoaction_linear_comp :
    (pointFiberCoaction f hf p).toLinearMap ∘ₗ (pointFiberMap (A := A) p).toLinearMap =
        TensorProduct.map (pointFiberMap (A := A) p).toLinearMap (Ideal.Quotient.mkₐ R
        (augmentationIdeal f)).toLinearMap ∘ₗ Coalgebra.comul := by
  ext a
  have h := pointFiberCoaction_map f hf p a
  change (pointFiberCoaction f hf p).toLinearMap
    ((pointFiberMap (A := A) p).toLinearMap a) = _ at h
  simp only [LinearMap.comp_apply]
  rw [h]
  change (TensorProduct.map (pointFiberMap (A := A) p).toLinearMap (LinearMap.id : (A ⧸
      augmentationIdeal f) →ₗ[R] (A ⧸ augmentationIdeal f)))
    ((TensorProduct.map (LinearMap.id : A →ₗ[R] A) (Ideal.Quotient.mkₐ R (augmentationIdeal
        f)).toLinearMap) (Coalgebra.comul a)) = _
  rw [← LinearMap.comp_apply, ← TensorProduct.map_comp]
  rfl

/-- Equality of linear maps out of the fibre can be checked on middle coordinates. -/
theorem pointFiber_linear_ext {M : Type*} [AddCommGroup M] [Module R M]
    (u v : (PointFiber (A := A) p) →ₗ[R] M) (h : ∀ a, u (pointFiberMap p a) = v (pointFiberMap p
        a)) : u = v := by
  let : Algebra B R := p.toRingHom.toAlgebra
  apply LinearMap.ext
  intro z
  change R ⊗[B] A at z
  induction z using TensorProduct.inductionOn with
  | tmul r a =>
    have hm : r ⊗ₜ[B] a = r • pointFiberMap (A := A) p a := by
      change r ⊗ₜ[B] a = r • ((1 : R) ⊗ₜ[B] a)
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hm, map_smul, map_smul, h]
  | add z w hz hw => simp only [map_add, hz, hw]

/-- Kernel comultiplication compatibility implies coassociativity on the fibre. -/
theorem pointFiberCoaction_coassoc
    (hδ : CoactionBasis.diagonal b ∘ₗ (Ideal.Quotient.mkₐ R (augmentationIdeal f)).toLinearMap =
        TensorProduct.map (Ideal.Quotient.mkₐ R (augmentationIdeal f)).toLinearMap
        (Ideal.Quotient.mkₐ R (augmentationIdeal f)).toLinearMap ∘ₗ Coalgebra.comul)
    (x : (PointFiber (A := A) p)) :
    TensorProduct.assoc R (PointFiber (A := A) p) (A ⧸ augmentationIdeal f) (A ⧸ augmentationIdeal
        f) (((pointFiberCoaction f hf p).toLinearMap).rTensor (A ⧸ augmentationIdeal f)
        ((pointFiberCoaction f hf p).toLinearMap x)) =
      (CoactionBasis.diagonal b).lTensor (PointFiber (A := A) p) ((pointFiberCoaction f hf
          p).toLinearMap x) := by
  have he : (TensorProduct.assoc R (PointFiber (A := A) p) (A ⧸ augmentationIdeal f) (A ⧸
      augmentationIdeal f)).toLinearMap ∘ₗ ((pointFiberCoaction f hf p).toLinearMap).rTensor (A ⧸
      augmentationIdeal f) ∘ₗ (pointFiberCoaction f hf p).toLinearMap =
      (CoactionBasis.diagonal b).lTensor (PointFiber (A := A) p) ∘ₗ (pointFiberCoaction f hf
          p).toLinearMap := by
    apply pointFiber_linear_ext p
    intro a
    exact Coalgebra.coaction_coassoc_on_image (pointFiberMap (A := A) p).toLinearMap
        (Ideal.Quotient.mkₐ R (augmentationIdeal f)).toLinearMap (pointFiberCoaction f hf
        p).toLinearMap (CoactionBasis.diagonal b)
      (pointFiberCoaction_linear_comp f hf p) hδ a
  exact LinearMap.congr_fun he x

end HopfAlgebra
