/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# The one-step loss of order for relative derivations

A relative derivation sends the (n+1)-st ideal power into the n-th power
of the target module filtration. Consequently a derivation on an original
algebra has well-defined values modulo I^n on its I^(n+1) neighborhoods.
This is the continuity estimate needed for completed cotangent comparisons.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicDerivationFiltration

variable {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module A M]
  (d : Derivation R A M) (I : Ideal A)

/-- A derivation lowers ideal-adic order by at most one. -/
theorem map_mem_pow_smul (n : ℕ) {a : A} (ha : a ∈ I ^ (n + 1)) :
    d a ∈ I ^ n • (⊤ : Submodule A M) := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [pow_succ'] at ha
    refine Submodule.mul_induction_on ha (fun a ha b hb ↦ ?_) (fun a b ha hb ↦ ?_)
    · rw [d.leibniz]
      apply Submodule.add_mem
      · rw [pow_succ', Submodule.mul_smul]
        exact Submodule.smul_mem_smul ha (ih hb)
      · exact Submodule.smul_mem_smul hb Submodule.mem_top
    · rw [map_add]
      exact Submodule.add_mem _ ha hb

/-- Congruent original sections have congruent derivatives one power lower. -/
theorem map_sub_mem_pow_smul (n : ℕ) {a b : A} (hab : a - b ∈ I ^ (n + 1)) :
    d a - d b ∈ I ^ n • (⊤ : Submodule A M) := by
  simpa only [map_sub] using map_mem_pow_smul d I n hab

/-- The derivative modulo I^n is determined by the original section modulo I^(n+1). -/
theorem quotient_eq (n : ℕ) {a b : A}
    (hab : Ideal.Quotient.mk (I ^ (n + 1)) a = Ideal.Quotient.mk (I ^ (n + 1)) b) :
    (Submodule.Quotient.mk (d a) : M ⧸ (I ^ n • (⊤ : Submodule A M))) =
      Submodule.Quotient.mk (d b) := by
  apply (Submodule.Quotient.eq _).mpr
  exact map_sub_mem_pow_smul d I n (Ideal.Quotient.eq.mp hab)

end FLT.Mazur.AdicDerivationFiltration
