/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.CartierReducedDifferential
public import FLT.GroupScheme.AugmentationCotangentNaturality

/-! # Original morphisms preserve the reduced Cartier differential -/

@[expose] public noncomputable section
open scoped TensorProduct
namespace HopfAlgebra.CartierDual
variable {R A D B C : Type} [CommRing R] [CommRing A] [CommRing D]
  [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]
  [HopfAlgebra R A] [HopfAlgebra R D]
  [Module.Finite R A] [Module.Free R A] [Module.Finite R D] [Module.Free R D]

/-- The linear pairing is natural for each original coordinate map and its transpose. -/
theorem linearTestEvaluation_naturality (f : A →ₐc[R] D)
    (ψ : CartierDual R A →ₗ[R] B) (d : D →ₗ[R] B) :
    linearTestEvaluation (ψ.comp (map f).toLinearMap) d =
      linearTestEvaluation ψ (d.comp f.toLinearMap) := by
  unfold linearTestEvaluation
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [← testLinearTensor_naturality f d]
  generalize testLinearTensor d = t
  induction t using TensorProduct.inductionOn with
  | tmul s φ => rfl
  | add t u ht hu => simp only [map_add, ht, hu]

/-- The differential of a reduced character can be computed with any cotangent coefficient lift. -/
theorem reducedLogDifferential_cotangent (q : B →ₐ[R] C) (hq : Function.Surjective q)
    (hJ : RingHom.ker q ^ 2 = ⊥) (ψ : CartierDual R A →ₐ[R] C)
    (χ : CartierDual R A →ₗ[R] B) (hχ : q.toLinearMap.comp χ = ψ.toLinearMap)
    (d : (RingHom.ker (Bialgebra.counitAlgHom R A)).Cotangent →ₗ[R] RingHom.ker q) :
    reducedLogDifferential q hq ψ ((Bialgebra.counitAlgHom R A).augmentationTangentEquiv d) =
      LinearMap.mul' R B
        ((((RingHom.ker q).subtype.restrictScalars R).comp d).rTensor B (linearTestDlog χ)) := by
  rw [reducedLogDifferential_eq_lift q hq hJ ψ χ hχ, linearTestDlog_pairing]
  rfl

/-- Cotangent extraction of an infinitesimal point computes its reduced differential. -/
theorem reducedLogDifferential_point_cotangent (q : B →ₐ[R] C)
    (hq : Function.Surjective q) (hJ : RingHom.ker q ^ 2 = ⊥)
    (ψ : CartierDual R A →ₐ[R] C)
    (f : (Bialgebra.counitAlgHom R A).AugmentationPointKernel q) :
    reducedLogDifferential q hq ψ (AlgHom.augmentationPointToTangent _ q hJ f) =
      LinearMap.mul' R B
        ((((RingHom.ker q).subtype.restrictScalars R).comp
          (AlgHom.augmentationPointCotangentEquiv _ q hJ f)).rTensor B
            (linearTestDlog (linearCharacterLift q hq ψ))) := by
  rw [← reducedLogDifferential_cotangent q hq hJ ψ _
    (linearCharacterLift_reduction q hq ψ)]
  change reducedLogDifferential q hq ψ _ = reducedLogDifferential q hq ψ
    ((Bialgebra.counitAlgHom R A).augmentationTangentEquiv
      ((Bialgebra.counitAlgHom R A).augmentationTangentEquiv.symm _))
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- Any linear coefficient lift gives the same cotangent contraction of a kernel point. -/
theorem reducedLogDifferential_point_lift (q : B →ₐ[R] C)
    (hq : Function.Surjective q) (hJ : RingHom.ker q ^ 2 = ⊥)
    (ψ : CartierDual R A →ₐ[R] C) (χ : CartierDual R A →ₗ[R] B)
    (hχ : q.toLinearMap.comp χ = ψ.toLinearMap)
    (f : (Bialgebra.counitAlgHom R A).AugmentationPointKernel q) :
    reducedLogDifferential q hq ψ (AlgHom.augmentationPointToTangent _ q hJ f) =
      LinearMap.mul' R B
        ((((RingHom.ker q).subtype.restrictScalars R).comp
          (AlgHom.augmentationPointCotangentEquiv _ q hJ f)).rTensor B (linearTestDlog χ)) := by
  rw [← reducedLogDifferential_cotangent q hq hJ ψ χ hχ]
  change reducedLogDifferential q hq ψ _ = reducedLogDifferential q hq ψ
    ((Bialgebra.counitAlgHom R A).augmentationTangentEquiv
      ((Bialgebra.counitAlgHom R A).augmentationTangentEquiv.symm _))
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- Pulling an infinitesimal point along an original model map preserves the pairing. -/
theorem reducedLogDifferential_precomp (q : B →ₐ[R] C) (hq : Function.Surjective q)
    (hJ : RingHom.ker q ^ 2 = ⊥) (f : A →ₐc[R] D)
    (ψ : CartierDual R A →ₐ[R] C)
    (d : (Bialgebra.counitAlgHom R D).augmentationTangent (M := RingHom.ker q))
    (e : (Bialgebra.counitAlgHom R A).augmentationTangent (M := RingHom.ker q))
    (he : e.val = d.val.comp f.toLinearMap) :
    reducedLogDifferential q hq (ψ.comp (map f)) d = reducedLogDifferential q hq ψ e := by
  let χ := linearCharacterLift q hq ψ
  have hχ : q.toLinearMap.comp (χ.comp (map f).toLinearMap) =
      (ψ.comp (map f)).toLinearMap := by
    rw [← LinearMap.comp_assoc, linearCharacterLift_reduction]
    rfl
  rw [reducedLogDifferential_eq_lift q hq hJ _ _ hχ,
    linearTestEvaluation_naturality]
  change _ = linearTestEvaluation χ (((RingHom.ker q).subtype.restrictScalars R).comp e.val)
  rw [he, LinearMap.comp_assoc]

end HopfAlgebra.CartierDual
