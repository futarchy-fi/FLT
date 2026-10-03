/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.ResidueNorm
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# First approximation to a norm of a unit

Finite-field norm surjectivity supplies a residue unit; local-ring unit
lifting supplies an integral unit with that residue. Its norm agrees with
the desired base unit modulo the maximal ideal. Higher approximations and
convergence are separate obligations.
-/

@[expose] public section

namespace LocalClassFieldTheory

open IsLocalRing

variable (R S : Type*) [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
  [Algebra R S] [IsLocalHom (algebraMap R S)]
  [Module.Finite R S] [Module.Free R S] [Algebra.FormallyUnramified R S]
  [Finite (ResidueField R)]

/-- A unit norm can match any prescribed base unit in the residue field. -/
theorem exists_unit_residue_norm (u : Rˣ) :
    ∃ v : Sˣ, residue R (Algebra.norm R (v : S)) = residue R (u : R) := by
  let := ResidueField.finite_of_finite (R := R) (S := S) inferInstance
  obtain ⟨w, hw⟩ := FiniteField.unitsMap_norm_surjective (ResidueField R) (ResidueField S)
    (Units.map (residue R).toMonoidHom u)
  obtain ⟨v, hv⟩ := surjective_units_map_of_local_ringHom (residue S)
    residue_surjective inferInstance w
  refine ⟨v, ?_⟩
  rw [residue_norm]
  have hv' : residue S (v : S) = (w : ResidueField S) := congrArg Units.val hv
  rw [hv']
  exact congrArg Units.val hw

/-- The first norm approximation has additive error in the maximal ideal. -/
theorem exists_unit_norm_sub_mem (u : Rˣ) :
    ∃ v : Sˣ, Algebra.norm R (v : S) - (u : R) ∈ maximalIdeal R := by
  obtain ⟨v, hv⟩ := exists_unit_residue_norm R S u
  exact ⟨v, (residue_eq_zero_iff _).mp (by rw [map_sub, hv, sub_self])⟩

end LocalClassFieldTheory
