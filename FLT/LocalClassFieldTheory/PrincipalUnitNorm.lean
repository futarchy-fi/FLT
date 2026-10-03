/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.PrincipalUnitResidue
public import FLT.LocalClassFieldTheory.NormFirstOrder
public import FLT.LocalClassFieldTheory.ResidueNorm

/-!
# Norm on graded principal units

The norm preserves the filtration, and the divided coefficient of its image
reduces to the residue-field trace in an unramified local algebra.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [Module.Free R S] [Module.Finite R S]

/-- Norm maps units at level n to units at level n. -/
def principalNorm (π : R) (n : ℕ) :
    principalUnits (algebraMap R S π) n →* principalUnits π n :=
  ((Units.map (Algebra.norm R)).comp (principalUnits (algebraMap R S π) n).subtype).codRestrict
    (principalUnits π n) (by
    intro v
    have hv : (v.val : S) = 1 + (π ^ n) • principalCoeff (algebraMap R S π) n v := by
      have h := principalCoeff_spec (algebraMap R S π) n v
      rw [Algebra.smul_def, map_pow]
      change (v.val : S) - 1 = _ at h
      exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)
    apply (mem_principalUnits π n _).2
    change π ^ n ∣ Algebra.norm R (v.val : S) - 1
    rw [hv]
    exact norm_one_add_pow_sub_one_dvd R S π n _)

/-- The restricted map is the ordinary algebra norm on values. -/
@[simp] theorem principalNorm_val (π : R) (n : ℕ)
    (u : principalUnits (algebraMap R S π) n) :
    ((principalNorm R S π n u).val : R) = Algebra.norm R (u.val : S) := rfl

variable [IsDomain R] {π : R} (hπ : π ≠ 0)

include hπ in
/-- The norm coefficient equals the trace coefficient up to a level-n error. -/
theorem principalNorm_coeff (n : ℕ) (u : principalUnits (algebraMap R S π) n) :
    ∃ a : R, principalCoeff π n (principalNorm R S π n u) =
      Algebra.trace R S (principalCoeff (algebraMap R S π) n u) + π ^ n * a := by
  have hu : (u.val : S) = 1 + (π ^ n) • principalCoeff (algebraMap R S π) n u := by
    have h := principalCoeff_spec (algebraMap R S π) n u
    rw [Algebra.smul_def, map_pow]
    exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)
  obtain ⟨a, ha⟩ := norm_one_add_smul R S (π ^ n) (principalCoeff (algebraMap R S π) n u)
  refine ⟨a, principalCoeff_eq hπ n _ _ ?_⟩
  rw [principalNorm_val, hu, ha]
  ring

variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
  [Algebra.FormallyUnramified R S]

include hπ in
/-- The norm on principal-unit symbols is the actual residue-field trace. -/
theorem principalNorm_residue (hm : π ∈ maximalIdeal R) (n : ℕ) (hn : 0 < n)
    (u : principalUnits (algebraMap R S π) n) :
    residue R (principalCoeff π n (principalNorm R S π n u)) =
      Algebra.trace (ResidueField R) (ResidueField S)
        (residue S (principalCoeff (algebraMap R S π) n u)) := by
  obtain ⟨a, ha⟩ := principalNorm_coeff R S hπ n u
  rw [ha, map_add, map_mul, residue_uniformizer_pow hm n hn, zero_mul, add_zero,
    residue_trace R S]

end LocalClassFieldTheory
