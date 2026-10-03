/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnitNormApproximation

/-!
# Compatible successive norm corrections

The recursion starts with the proved residue norm lift and uses the proved
one-step correction. Its norm precision and successive congruences hold at
every index, with no assumed sequence or arithmetic lifting contract.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing

variable (R S : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [IsLocalHom (algebraMap R S)]
  [Module.Free R S] [Module.Finite R S] [Algebra.FormallyUnramified R S]
  [Finite (ResidueField R)] {π : R} (hπ : Irreducible π)

/-- The n-th approximation has norm correct through level n+1. -/
def unitNormApproximation (u : Rˣ) :
    (n : ℕ) → {v : Sˣ // Units.map (Algebra.norm R) v / u ∈ principalUnits π (n + 1)}
  | 0 => ⟨(exists_unit_norm_initial R S hπ u).choose,
      (exists_unit_norm_initial R S hπ u).choose_spec⟩
  | n + 1 =>
      let v := unitNormApproximation u n
      let h := exists_unit_norm_improvement R S hπ u (n + 1) (by omega) v.val v.property
      ⟨h.choose, h.choose_spec.1⟩

/-- Each new approximation preserves the previous precision upstairs. -/
theorem unitNormApproximation_step (u : Rˣ) (n : ℕ) :
    (algebraMap R S π) ^ (n + 1) ∣
      ((unitNormApproximation R S hπ u (n + 1)).val : S) -
        ((unitNormApproximation R S hπ u n).val : S) := by
  exact (exists_unit_norm_improvement R S hπ u (n + 1) (by omega)
    (unitNormApproximation R S hπ u n).val
    (unitNormApproximation R S hπ u n).property).choose_spec.2

/-- The norm error is divisible by the next power at each index. -/
theorem unitNormApproximation_norm (u : Rˣ) (n : ℕ) :
    π ^ (n + 1) ∣ Algebra.norm R ((unitNormApproximation R S hπ u n).val : S) - (u : R) :=
  (unit_div_mem_principalUnits π (n + 1) _ _).1
    (unitNormApproximation R S hπ u n).property

end LocalClassFieldTheory
