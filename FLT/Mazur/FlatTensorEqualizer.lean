/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Flat.Basic

/-!
# Flat scalar extension of the actual equalizer of two coefficient maps

Flatness preserves the kernel of the difference of the two original maps.
Consequently every invariant tensor lifts uniquely from the tensor product
of the original equalizer. No finite generation hypothesis is needed.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.FlatTensorEqualizer
variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] (p q : M →ₗ[R] N)

/-- The actual full coefficient equalizer, expressed as a kernel. -/
def equalizer : Submodule R M := LinearMap.ker (p - q)

/-- Membership is equality of the original two coefficient maps. -/
theorem mem_equalizer (m : M) : m ∈ equalizer p q ↔ p m = q m := by
  simp only [equalizer, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]

variable (B : Type*) [AddCommGroup B] [Module R B]

/-- Equality of the two base-changed coefficient maps is the tensor kernel condition. -/
theorem tensor_difference_zero_iff (x : B ⊗[R] M) :
    (p - q).lTensor B x = 0 ↔ p.lTensor B x = q.lTensor B x := by
  rw [LinearMap.lTensor_sub, LinearMap.sub_apply, sub_eq_zero]

variable [Module.Flat R B]

/-- The original equalizer remains embedded after flat scalar extension. -/
theorem inclusion_injective : Function.Injective ((equalizer p q).subtype.lTensor B) :=
  Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective

/-- Every invariant tensor has a unique preimage from the original invariant module. -/
theorem existsUnique_lift (x : B ⊗[R] M) (hx : p.lTensor B x = q.lTensor B x) :
    ∃! y : B ⊗[R] equalizer p q, (equalizer p q).subtype.lTensor B y = x := by
  have he := Module.Flat.lTensor_exact B (LinearMap.exact_subtype_ker_map (p - q))
  obtain ⟨y, hy⟩ := (he x).mp ((tensor_difference_zero_iff p q B x).mpr hx)
  exact ⟨y, hy, fun _ hz ↦ inclusion_injective p q B (hz.trans hy.symm)⟩

/-- The range is exactly the equalizer of the two actual tensor maps. -/
theorem range_inclusion : LinearMap.range ((equalizer p q).subtype.lTensor B) =
    equalizer (p.lTensor B) (q.lTensor B) := by
  ext x
  rw [mem_equalizer]
  exact ((Module.Flat.lTensor_exact B
    (LinearMap.exact_subtype_ker_map (p - q))) x).symm.trans
      (tensor_difference_zero_iff p q B x)

/-- The comparison is an isomorphism onto the complete base-changed equalizer. -/
def comparison : B ⊗[R] equalizer p q ≃ₗ[R] equalizer (p.lTensor B) (q.lTensor B) :=
  (LinearEquiv.ofInjective ((equalizer p q).subtype.lTensor B) (inclusion_injective p q B)).trans
    (LinearEquiv.ofEq _ _ (range_inclusion p q B))

/-- The comparison is precisely the original tensor inclusion. -/
theorem comparison_val (x : B ⊗[R] equalizer p q) :
    (comparison p q B x).val = (equalizer p q).subtype.lTensor B x := rfl

end FLT.Mazur.FlatTensorEqualizer
