/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.NumberField.Completion.Different

/-! # The integral rank at a finite place is bounded by the global degree -/

@[expose] public noncomputable section

open IsDedekindDomain.HeightOneSpectrum

attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion

namespace NumberField

variable (L : Type*) [Field L] [NumberField L]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) (w : v.Extension (𝓞 L))

/-- Each local field degree is one nonnegative summand of the global degree. -/
theorem completion_finrank_le_global :
    Module.finrank (v.adicCompletion ℚ) (w.1.adicCompletion L) ≤ Module.finrank ℚ L := by
  classical
  let := Extension.fintype (𝓞 ℚ) ℚ L (𝓞 L) v
  rw [← adicCompletion.ramificationIdx_mul_inertiaDeg_eq_finrank ℚ L w,
    ← Ideal.sum_ramification_inertia_extensions (𝓞 ℚ) ℚ L (𝓞 L) v]
  exact Finset.single_le_sum (f := fun x : v.Extension (𝓞 L) ↦
    x.1.asIdeal.ramificationIdx (𝓞 ℚ) * x.1.asIdeal.inertiaDeg (𝓞 ℚ))
    (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ w)

/-- Passing to fraction fields identifies integral and field ranks. -/
theorem completionIntegers_finrank_eq :
    Module.finrank (v.adicCompletionIntegers ℚ) (w.1.adicCompletionIntegers L) =
      Module.finrank (v.adicCompletion ℚ) (w.1.adicCompletion L) := by
  let : IsScalarTower (v.adicCompletionIntegers ℚ) (w.1.adicCompletionIntegers L)
      (w.1.adicCompletion L) := .of_algebraMap_eq fun _ ↦ rfl
  let : FaithfulSMul (v.adicCompletionIntegers ℚ) (w.1.adicCompletionIntegers L) :=
    FaithfulSMul.of_field_isFractionRing _ _ (v.adicCompletion ℚ) (w.1.adicCompletion L)
  exact (IsFractionRing.finrank_eq (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)
    (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)).symm

/-- The actual completed integer ring has integral rank at most the global degree. -/
theorem completionIntegers_finrank_le_global :
    Module.finrank (v.adicCompletionIntegers ℚ) (w.1.adicCompletionIntegers L) ≤
      Module.finrank ℚ L := by
  rw [completionIntegers_finrank_eq]
  exact completion_finrank_le_global L v w

end NumberField
