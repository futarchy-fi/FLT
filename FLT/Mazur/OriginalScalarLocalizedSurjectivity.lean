/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteKernelCorrectionLocalization
public import Mathlib.RingTheory.Localization.Module

/-!
# Exact numerator tests for localized boundary surjectivity

Surjectivity is equivalent to lifting each original boundary coefficient
after its own original denominator. Neither finite generation nor a common
denominator is required. Fraction equality is cleared on the original modules.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.OriginalScalarLocalizedSurjectivity
variable {R A B : Type*} [CommRing R] [AddCommGroup A] [AddCommGroup B]
  [Module R A] [Module R B] (β : A →ₗ[R] B) (S : Submonoid R)

/-- The existing original-denominator criterion also applies over the localized scalar ring. -/
theorem fraction_mem_range_iff (b : B) :
    LocalizedModule.mk b (1 : S) ∈ LinearMap.range (LocalizedModule.map S β) ↔
      ∃ s : S, ∃ a : A, β a = s.val • b := by
  exact FiniteKernelCorrections.localized_mem_range_iff S β b

/-- Every coefficient may use its own denominator, with no finite boundary hypothesis. -/
theorem surjective_iff : Function.Surjective (LocalizedModule.map S β) ↔
    ∀ b : B, ∃ s : S, ∃ a : A, β a = s.val • b := by
  constructor
  · intro h b
    exact (fraction_mem_range_iff β S b).mp (h (LocalizedModule.mk b 1))
  · intro h b
    induction b using LocalizedModule.induction_on with
    | _ b s =>
      obtain ⟨r, a, ha⟩ := h b
      refine ⟨LocalizedModule.mk a (r * s), ?_⟩
      rw [LocalizedModule.map_mk]
      rw [ha]
      exact LocalizedModule.mk_cancel_common_left r s b

/-- Restricting to the actual compatible submodule preserves its equation in every numerator. -/
theorem compatible_surjective_iff (N : Submodule R A) :
    Function.Surjective (LocalizedModule.map S (β.comp N.subtype)) ↔
      ∀ b : B, ∃ s : S, ∃ a : A, a ∈ N ∧ β a = s.val • b := by
  rw [surjective_iff]
  constructor
  · intro h b
    obtain ⟨s, a, ha⟩ := h b
    exact ⟨s, a.val, a.property, ha⟩
  · intro h b
    obtain ⟨s, a, ha, hab⟩ := h b
    exact ⟨s, ⟨a, ha⟩, hab⟩

end FLT.Mazur.OriginalScalarLocalizedSurjectivity
