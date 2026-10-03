/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.PadicTilt

/-! # Frobenius surjectivity for the actual integer ring modulo p -/

@[expose] public noncomputable section
open scoped NNReal
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- Algebraic closedness supplies a p-th root which remains integral. -/
theorem complexInteger_pow_surjective : Function.Surjective (fun x : 𝓞_ℂ_[p] ↦ x ^ p) := by
  intro x
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (x : ℂ_[p]) (Fact.out : p.Prime).pos
  have hint : y ∈ PadicComplexInt p := by
    change Valued.v y ≤ 1
    apply (pow_le_one_iff_of_nonneg (zero_le : (0 : ℝ≥0) ≤ Valued.v y)
      (Fact.out : p.Prime).ne_zero).mp
    rw [← map_pow, hy]
    exact x.property
  exact ⟨⟨y, hint⟩, Subtype.ext hy⟩

/-- Frobenius on O_C/(p) is surjective, the input to the actual theta surjectivity theorem. -/
theorem complexInteger_frobenius_surjective :
    Function.Surjective (frobenius (ModP 𝓞_ℂ_[p] p) p) := by
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, hb⟩ := complexInteger_pow_surjective p a
  refine ⟨Ideal.Quotient.mk _ b, ?_⟩
  change (Ideal.Quotient.mk _ b) ^ p = Ideal.Quotient.mk _ a
  change b ^ p = a at hb
  rw [← map_pow, hb]

end PadicHodgeTheory
