/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.NumberTheory.Padics.RingHoms

/-! # Uniqueness of the prime residue map from the p-adic integers -/

@[expose] public section

namespace GaloisRepresentation.IsHardlyRamified

/-- Every ring map from the p-adic integers to their prime residue field is
the canonical reduction map, without any continuity assumption. -/
theorem primeResidueMap_unique (p : ℕ) [Fact p.Prime]
    (f : ℤ_[p] →+* ZMod p) : f = PadicInt.toZMod := by
  have hker : IsLocalRing.maximalIdeal ℤ_[p] ≤ RingHom.ker f := by
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_le]
    intro y hy
    simp only [Set.mem_singleton_iff] at hy
    subst y
    change f (p : ℤ_[p]) = 0
    simp
  ext x
  have h := hker (PadicInt.toZMod_spec (x := x))
  change f (x - (ZMod.cast (PadicInt.toZMod x) : ℤ_[p])) = 0 at h
  change f x = (x.zmodRepr : ZMod p)
  simpa [map_sub, ZMod.cast_eq_val, sub_eq_zero] using h

end GaloisRepresentation.IsHardlyRamified
