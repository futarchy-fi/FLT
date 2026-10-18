/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeNaturalUnitLocus
public import Mathlib.Data.Nat.Choose.Lucas
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Strict-subframe unit-degree covers away from prime-power frame sizes

For a frame size greater than one that is not a prime power, the strict
binomial degrees have gcd one. At each original scheme point at least one
such degree is a unit in the stalk. Their actual principal opens therefore
cover the scheme. This does not supply target charts or selection-error vanishing.
-/

@[expose] public noncomputable section
open AlgebraicGeometry
namespace FLT.Mazur.SubframeDegreeUnitCover
open SchemeNaturalUnitLocus

/-- A finite family of natural numbers with gcd one has a unit in any local ring. -/
theorem exists_isUnit_of_gcd_one {R : Type*} [CommRing R] [IsLocalRing R]
    (s : Finset ℕ) (d : ℕ → ℕ) (hd : s.gcd d = 1) :
    ∃ m ∈ s, IsUnit (d m : R) := by
  classical
  by_contra! hh
  let K := IsLocalRing.ResidueField R
  have hzero (m : ℕ) (hm : m ∈ s) : (d m : K) = 0 := by
    have h := mt (IsLocalRing.residue_ne_zero_iff_isUnit (d m : R)).mp (hh m hm)
    simpa only [map_natCast, not_not] using h
  have hdiv : ringChar K ∣ s.gcd d := Finset.dvd_gcd_iff.mpr fun m hm ↦
    (CharP.cast_eq_zero_iff K (ringChar K) (d m)).mp (hzero m hm)
  rw [hd] at hdiv
  have h1 := (CharP.cast_eq_zero_iff K (ringChar K) 1).mpr hdiv
  exact one_ne_zero (by simpa only [Nat.cast_one] using h1)

/-- Non-prime-power frame sizes supply a strict positive selection degree at every local ring. -/
theorem exists_binomial_isUnit {R : Type*} [CommRing R] [IsLocalRing R]
    (n : ℕ) (hn : 1 < n) (hp : ¬ IsPrimePow n) :
    ∃ m ∈ Finset.Icc 1 (n - 1), IsUnit (n.choose m : R) :=
  exists_isUnit_of_gcd_one _ _ (Choose.gcd_choose_eq_one_of_not_isPrimePow hn hp)

/-- The principal opens of strict selection degrees cover the original, unreduced scheme. -/
theorem iSup_binomial_locus (X : Scheme.{0}) (n : ℕ) (hn : 1 < n)
    (hp : ¬ IsPrimePow n) :
    (⨆ m : {m // m ∈ Finset.Icc 1 (n - 1)}, locus X (n.choose m.val)) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨m, hm, hu⟩ := exists_binomial_isUnit (R := X.presheaf.stalk x) n hn hp
  exact (le_iSup (fun m : {m // m ∈ Finset.Icc 1 (n - 1)} ↦
    locus X (n.choose m.val)) ⟨m, hm⟩) ((mem_iff X (n.choose m) x).mpr hu)

/-- Every point of an affine chart has a canonical affine unit-degree refinement. -/
theorem exists_affine_unit_refinement (X : Scheme.{0}) (n : ℕ) (hn : 1 < n)
    (hp : ¬ IsPrimePow n) (U : X.Opens) (hU : IsAffineOpen U) (x : X) (hx : x ∈ U) :
    ∃ m ∈ Finset.Icc 1 (n - 1),
      x ∈ U ⊓ locus X (n.choose m) ∧ IsAffineOpen (U ⊓ locus X (n.choose m)) ∧
        IsUnit (n.choose m : Γ((U ⊓ locus X (n.choose m)).toScheme, ⊤)) := by
  obtain ⟨m, hm, hu⟩ := exists_binomial_isUnit (R := X.presheaf.stalk x) n hn hp
  exact ⟨m, hm, mem_inter X _ U x hx hu, isAffineOpen_inter X _ U hU,
    isUnit_on X _ _ inf_le_right⟩

/-- Prime-power frames have no strict unit degree in their defining residue characteristic. -/
theorem not_mem_prime_power_locus (X : Scheme.{0}) (x : X) (p k m : ℕ)
    (hp : p.Prime) (hm : 0 < m) (hmn : m < p ^ k)
    [CharP (IsLocalRing.ResidueField (X.presheaf.stalk x)) p] :
    x ∉ locus X ((p ^ k).choose m) := by
  rw [mem_iff, ← IsLocalRing.residue_ne_zero_iff_isUnit, map_natCast]
  exact not_not.mpr ((CharP.cast_eq_zero_iff
    (IsLocalRing.ResidueField (X.presheaf.stalk x)) p _).mpr
      (hp.dvd_choose_pow (Nat.ne_of_gt hm) (Nat.ne_of_lt hmn)))

end FLT.Mazur.SubframeDegreeUnitCover
