/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FlatIdealTensor
public import Mathlib.RingTheory.Flat.Localization

/-!
# Transporting a fixed ideal tensor test through flat target extensions

Scalar cancellation identifies the new multiplication map with the flat
extension of the old one. This preserves injectivity, in particular when
the target algebra is localized, without requiring flatness over the base.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.IdealInclusionFlatExtension
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  (T : Type*) [CommRing T] [Algebra R T] [Algebra A T] [IsScalarTower R A T]

/-- Cancel the intermediate target algebra in the actual ideal multiplication square. -/
theorem inclusion_cancel (I : Ideal R) (z : T ⊗[A] (A ⊗[R] I)) :
    FCurve.idealTensorInclusion I (AlgebraTensorModule.cancelBaseChange R A T T I z) =
      AlgebraTensorModule.rid A T T
        ((FCurve.idealTensorInclusion (S := A) I).lTensor T z) := by
  induction z with
  | tmul t x =>
    induction x with
    | tmul a i =>
      simp only [AlgebraTensorModule.cancelBaseChange_tmul,
        FCurve.idealTensorInclusion_tmul, LinearMap.lTensor_tmul,
        AlgebraTensorModule.rid_tmul, Algebra.smul_def, map_mul]
      rw [IsScalarTower.algebraMap_apply R A T]
      ring
    | add x y hx hy => simp only [tmul_add, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- A flat extension of the target preserves injectivity for this particular base ideal. -/
theorem injective [Module.Flat A T] (I : Ideal R)
    (h : Function.Injective (FCurve.idealTensorInclusion (S := A) I)) :
    Function.Injective (FCurve.idealTensorInclusion (S := T) I) := by
  intro x y hxy
  apply (AlgebraTensorModule.cancelBaseChange R A T T I).symm.injective
  apply Module.Flat.lTensor_preserves_injective_linearMap
    (FCurve.idealTensorInclusion (S := A) I) h
  apply (AlgebraTensorModule.rid A T T).injective
  rw [← inclusion_cancel T I, ← inclusion_cancel T I,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  exact hxy

/-- The ideal test survives every localization of the target algebra. -/
theorem localization_injective (U : Submonoid A) [IsLocalization U T] (I : Ideal R)
    (h : Function.Injective (FCurve.idealTensorInclusion (S := A) I)) :
    Function.Injective (FCurve.idealTensorInclusion (S := T) I) := by
  let _ := IsLocalization.flat T U
  exact injective T I h

end FLT.Mazur.IdealInclusionFlatExtension
