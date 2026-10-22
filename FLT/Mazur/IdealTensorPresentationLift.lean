/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealTensorPresentationCriterion

/-!
# Explicit lifts comparing ideal and presentation obstructions

The two tensor kernels are related by concrete witnesses in a presentation.
These witnesses keep the comparison available for changing both the ring
and the module, instead of only comparing whether the kernels vanish.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.IdealTensorPresentationLift
open TensorKernelExtension
variable {R P N M : Type*} [CommRing R]
  [AddCommGroup P] [Module R P] [AddCommGroup N] [Module R N]
  [AddCommGroup M] [Module R M]
  (f : P →ₗ[R] N) (q : N →ₗ[R] M)
  (he : Function.Exact f q) (hq : Function.Surjective q) (I : Ideal R)

include he hq

/-- An ideal obstruction gives an actual relation in the reduced presentation. -/
theorem lift_ideal_kernel (z : I ⊗[R] M) (hz : I.subtype.rTensor M z = 0) :
    ∃ (t : I ⊗[R] N) (u : R ⊗[R] P),
      q.lTensor I t = z ∧ f.lTensor R u = I.subtype.rTensor N t ∧
      f.lTensor (R ⧸ I) (I.mkQ.rTensor P u) = 0 := by
  obtain ⟨t, rfl⟩ := LinearMap.lTensor_surjective I hq z
  have ht : q.lTensor R (I.subtype.rTensor N t) = 0 := by
    rw [differential_naturality]
    exact hz
  obtain ⟨u, hu⟩ := (lTensor_exact R he hq _).mp ht
  refine ⟨t, u, rfl, hu, ?_⟩
  rw [differential_naturality, hu]
  exact (rTensor_exact N (LinearMap.exact_subtype_mkQ I)
    I.mkQ_surjective).apply_apply_eq_zero t

/-- Conversely every reduced presentation relation supplies an ideal obstruction. -/
theorem lift_quotient_kernel (z : (R ⧸ I) ⊗[R] P)
    (hz : f.lTensor (R ⧸ I) z = 0) :
    ∃ (u : R ⊗[R] P) (t : I ⊗[R] N),
      I.mkQ.rTensor P u = z ∧ I.subtype.rTensor N t = f.lTensor R u ∧
      I.subtype.rTensor M (q.lTensor I t) = 0 := by
  obtain ⟨u, rfl⟩ := LinearMap.rTensor_surjective P I.mkQ_surjective z
  have hu : I.mkQ.rTensor N (f.lTensor R u) = 0 := by
    rw [← differential_naturality]
    exact hz
  obtain ⟨t, ht⟩ := (rTensor_exact N (LinearMap.exact_subtype_mkQ I)
    I.mkQ_surjective _).mp hu
  refine ⟨u, t, rfl, ht, ?_⟩
  rw [← differential_naturality, ht]
  exact (lTensor_exact R he hq).apply_apply_eq_zero u

/-- Vanishing of the ideal obstruction forces vanishing of its reduced relation. -/
theorem quotient_zero_of_ideal_zero (hf : Function.Injective f)
    (t : I ⊗[R] N) (u : R ⊗[R] P)
    (hu : f.lTensor R u = I.subtype.rTensor N t) (ht : q.lTensor I t = 0) :
    I.mkQ.rTensor P u = 0 := by
  obtain ⟨v, hv⟩ := (lTensor_exact I he hq t).mp ht
  have huv : u = I.subtype.rTensor P v := by
    apply Module.Flat.lTensor_preserves_injective_linearMap f hf
    rw [differential_naturality, hv, hu]
  rw [huv]
  exact (rTensor_exact P (LinearMap.exact_subtype_mkQ I)
    I.mkQ_surjective).apply_apply_eq_zero v

/-- Flatness of the middle term gives the converse vanishing implication. -/
theorem ideal_zero_of_quotient_zero [Module.Flat R N]
    (t : I ⊗[R] N) (u : R ⊗[R] P)
    (hu : f.lTensor R u = I.subtype.rTensor N t) (hz : I.mkQ.rTensor P u = 0) :
    q.lTensor I t = 0 := by
  obtain ⟨v, hv⟩ := (rTensor_exact P (LinearMap.exact_subtype_mkQ I)
    I.mkQ_surjective u).mp hz
  have htv : t = f.lTensor I v := by
    apply Module.Flat.rTensor_preserves_injective_linearMap I.subtype I.subtype_injective
    rw [← differential_naturality, hv, hu]
  rw [htv]
  exact (lTensor_exact I he hq).apply_apply_eq_zero v

end FLT.Mazur.IdealTensorPresentationLift
