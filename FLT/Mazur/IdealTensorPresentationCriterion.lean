/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TensorKernelExtension

/-!
# Comparing ideal kernels with a flat presentation

For an exact presentation with flat middle term, injectivity of the ideal
tensor for its cokernel is equivalent to injectivity of the presentation
inclusion after quotienting the base by that ideal. Both directions are
explicit tensor diagram chases.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.IdealTensorPresentationCriterion
open TensorKernelExtension
variable {R P N M : Type*} [CommRing R]
  [AddCommGroup P] [Module R P] [AddCommGroup N] [Module R N]
  [AddCommGroup M] [Module R M] [Module.Flat R N]
  (f : P →ₗ[R] N) (q : N →ₗ[R] M)
  (he : Function.Exact f q) (hq : Function.Surjective q)

include he hq

/-- A quotient test for the presentation implies the corresponding ideal test. -/
theorem ideal_injective (I : Ideal R)
    (h : Function.Injective (f.lTensor (R ⧸ I))) :
    Function.Injective (I.subtype.rTensor M) := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro z hz
  change z = 0
  obtain ⟨t, rfl⟩ := LinearMap.lTensor_surjective I hq z
  have ht : q.lTensor R (I.subtype.rTensor N t) = 0 := by
    rw [differential_naturality]
    exact hz
  obtain ⟨u, hu⟩ := (lTensor_exact R he hq _).mp ht
  have hu0 : I.mkQ.rTensor P u = 0 := by
    apply h
    rw [map_zero, differential_naturality, hu]
    exact (rTensor_exact N (LinearMap.exact_subtype_mkQ I)
      I.mkQ_surjective).apply_apply_eq_zero t
  obtain ⟨v, hv⟩ := (rTensor_exact P (LinearMap.exact_subtype_mkQ I)
    I.mkQ_surjective u).mp hu0
  have htv : t = f.lTensor I v := by
    apply Module.Flat.rTensor_preserves_injective_linearMap I.subtype I.subtype_injective
    rw [← differential_naturality, hv, hu]
  rw [htv]
  exact (lTensor_exact I he hq).apply_apply_eq_zero v

omit [Module.Flat R N] in
/-- Conversely the ideal test gives injectivity of an actual presentation inclusion. -/
theorem quotient_injective (hf : Function.Injective f) (I : Ideal R)
    (h : Function.Injective (I.subtype.rTensor M)) :
    Function.Injective (f.lTensor (R ⧸ I)) := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro z hz
  change z = 0
  obtain ⟨v, hv⟩ := LinearMap.rTensor_surjective P I.mkQ_surjective z
  have hv0 : I.mkQ.rTensor N (f.lTensor R v) = 0 := by
    rw [← differential_naturality, hv]
    exact hz
  obtain ⟨w, hw⟩ := (rTensor_exact N (LinearMap.exact_subtype_mkQ I)
    I.mkQ_surjective _).mp hv0
  have hw0 : q.lTensor I w = 0 := by
    apply h
    rw [map_zero, ← differential_naturality, hw]
    exact (lTensor_exact R he hq).apply_apply_eq_zero v
  obtain ⟨t, ht⟩ := (lTensor_exact I he hq w).mp hw0
  have hv' : v = I.subtype.rTensor P t := by
    apply Module.Flat.lTensor_preserves_injective_linearMap f hf
    rw [differential_naturality, ht, hw]
  rw [← hv, hv']
  exact (rTensor_exact P (LinearMap.exact_subtype_mkQ I)
    I.mkQ_surjective).apply_apply_eq_zero t

end FLT.Mazur.IdealTensorPresentationCriterion
