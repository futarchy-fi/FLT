/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocalizedTensorCancellation
public import Mathlib.Algebra.Exact.Basic

/-!
# Exactness after cancelling localized tensor coefficients

The fraction-preserving tensor comparisons identify exact pairs, allowing a
residue-field complex over the original ring to be used over its local ring.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.LocalizedTensorCancellation

variable {R : Type} [CommRing R] (S : Submonoid R)
  (B : Type) [AddCommGroup B] [Module R B] [Module (Localization S) B]
  [IsScalarTower R (Localization S) B]
  {M N P : Type} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

/-- Cancelling localization preserves and reflects exactness of the original tensor pair. -/
theorem tensor_exact_iff (d : M →ₗ[R] N) (e : N →ₗ[R] P) :
    Function.Exact ((LocalizedModule.map S d).lTensor B)
      ((LocalizedModule.map S e).lTensor B) ↔
        Function.Exact (d.lTensor B) (e.lTensor B) := by
  exact LinearMap.exact_iff_of_surjective_of_bijective_of_injective
    (((LocalizedModule.map S d).lTensor B).restrictScalars R)
    (((LocalizedModule.map S e).lTensor B).restrictScalars R)
    (d.lTensor B) (e.lTensor B)
    ((tensorEquiv S B M).toLinearMap.restrictScalars R)
    ((tensorEquiv S B N).toLinearMap.restrictScalars R)
    ((tensorEquiv S B P).toLinearMap.restrictScalars R)
    (LinearMap.ext fun x ↦ (tensorEquiv_map S B d x).symm)
    (LinearMap.ext fun x ↦ (tensorEquiv_map S B e x).symm)
    (tensorEquiv S B M).surjective (tensorEquiv S B N).bijective
    (tensorEquiv S B P).injective

end FLT.Mazur.LocalizedTensorCancellation
