/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic

/-!
# Adic completeness and powers of an ideal

Completeness for a positive power of an ideal implies completeness for the
ideal itself, by taking a cofinal subsequence of any adic Cauchy sequence.
-/

@[expose] public section

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Completeness for a positive ideal power implies completeness for the ideal. -/
theorem IsAdicComplete.ofPow (I : Ideal R) {e : ℕ} (he : 0 < e)
    [IsAdicComplete (I ^ e) M] : IsAdicComplete I M := by
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    exact IsHausdorff.haus (inferInstance : IsHausdorff (I ^ e) M) x
      (fun n => by simpa only [pow_mul] using hx (e * n))
  · intro f hf
    have hc : ∀ {m n : ℕ}, m ≤ n →
        f (e * m) ≡ f (e * n) [SMOD ((I ^ e) ^ m • ⊤ : Submodule R M)] := by
      intro m n hmn
      simpa only [pow_mul] using hf (Nat.mul_le_mul_left e hmn)
    obtain ⟨x, hx⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete (I ^ e) M) hc
    refine ⟨x, fun n => ?_⟩
    have hn : n ≤ e * n := by nlinarith
    apply (hf hn).trans
    apply SModEq.mono (Submodule.smul_mono_left (Ideal.pow_le_pow_right hn))
    simpa only [pow_mul] using hx n
