/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.B5Inputs

/-! # Freeness of a finite domain quotient avoiding the coefficient prime -/

@[expose] public section

namespace GaloisRepresentation.IsHardlyRamified

/-- A prime quotient of a finite p-adic algebra is free over the p-adic integers
if the prime ideal avoids `p`. Freeness of the original algebra is not needed. -/
theorem quotient_free_of_prime_avoiding_p (p : ℕ) [Fact p.Prime]
    (D : Type) [CommRing D] [Algebra ℤ_[p] D] [Module.Finite ℤ_[p] D]
    (P : Ideal D) [P.IsPrime] (hp : (p : D) ∉ P) :
    Module.Free ℤ_[p] (D ⧸ P) := by
  have hinj : Function.Injective (algebraMap ℤ_[p] (D ⧸ P)) := by
    apply (RingHom.injective_iff_ker_eq_bot _).mpr
    by_contra hker
    obtain ⟨n, hn⟩ := PadicInt.ideal_eq_span_pow_p hker
    have hmem : (p : ℤ_[p]) ^ n ∈ RingHom.ker (algebraMap ℤ_[p] (D ⧸ P)) := by
      rw [hn]
      exact Ideal.subset_span (Set.mem_singleton _)
    have hzero : algebraMap ℤ_[p] (D ⧸ P) ((p : ℤ_[p]) ^ n) = 0 := hmem
    apply hp
    apply (inferInstance : P.IsPrime).mem_of_pow_mem n
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [map_pow, map_natCast] using hzero
  let : Module.IsTorsionFree ℤ_[p] (D ⧸ P) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  infer_instance

end GaloisRepresentation.IsHardlyRamified
