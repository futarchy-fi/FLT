/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudFiniteValuation

/-!
# Natural orders under uniformizer-preserving extension

A nonzero element is a unit times a power of a uniformizer. When that
uniformizer stays irreducible, the same factorization computes its order.
-/

@[expose] public noncomputable section
namespace RaynaudParameters
open IsDiscreteValuationRing

variable {R S : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] (f : R →+* S)

/-- Preserving one uniformizer preserves the natural order of every nonzero element. -/
theorem order_map_of_uniformizer {π : R} (hπ : Irreducible π)
    (hπS : Irreducible (f π)) {a : R} (ha : a ≠ 0) : order (f a) = order a := by
  obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible ha hπ
  simp only [order, map_mul, map_pow, addVal_mul, addVal_pow,
    addVal_uniformizer hπ, addVal_uniformizer hπS, addVal_eq_zero_of_unit,
    addVal_eq_zero_iff.mpr (u.isUnit.map f), zero_add]

end RaynaudParameters
