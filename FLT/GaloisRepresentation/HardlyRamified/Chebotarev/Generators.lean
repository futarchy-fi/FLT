/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.SetLike.Fintype
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Order.Atoms.Finite

/-!
# Inclusion-exclusion for generators of a finite cyclic group

This is leaf H1 of `docs/CHEBOTAREV_PLAN.md`. Maximal proper subgroups
detect nongenerators in any finite group. In a cyclic group, averaging
their inclusion-exclusion formula gives `φ(|H|) / |H|`.

The plan's `Max` and `D` are defined in the `Chebotarev` namespace, with
the ambient group explicit in `D H J`. The indicator theorem only needs
`[Finite H]`; cyclicity is required for the density coefficient. No
nontriviality hypothesis is needed, so both statements include the trivial group.
-/

@[expose] public section

open scoped BigOperators

namespace Chebotarev

variable (H : Type*) [Group H] [Finite H]

/-- The maximal proper subgroups of `H`. -/
abbrev Max := {D : Subgroup H // IsCoatom D}

noncomputable instance : Fintype (Max H) := Fintype.ofFinite _

/-- The intersection of a finite family of maximal proper subgroups.
The empty intersection is the whole group. -/
def D (J : Finset (Max H)) : Subgroup H := ⨅ M ∈ J, M.1

variable {H}

/-- A finite-group element generates the group exactly when it avoids every
maximal proper subgroup. -/
theorem zpowers_eq_top_iff_forall_not_mem_max (a : H) :
    Subgroup.zpowers a = ⊤ ↔ ∀ M : Max H, a ∉ M.1 := by
  constructor
  · intro ha M hmem
    have hle : Subgroup.zpowers a ≤ M.1 := Subgroup.zpowers_le.mpr hmem
    exact M.2.ne_top (top_le_iff.mp (ha ▸ hle))
  · intro ha
    rcases eq_top_or_exists_le_coatom (Subgroup.zpowers a) with h | ⟨M, hM, hle⟩
    · exact h
    · exact False.elim (ha ⟨M, hM⟩ (hle (Subgroup.mem_zpowers a)))

open Classical in
/-- Inclusion-exclusion over maximal proper subgroups is the generator indicator. -/
theorem generator_indicator (a : H) :
    (if Subgroup.zpowers a = ⊤ then (1 : ℝ) else 0) =
      ∑ J ∈ (Finset.univ : Finset (Max H)).powerset,
        (-1 : ℝ) ^ J.card * (if a ∈ D H J then 1 else 0) := by
  have hprod : (∏ M : Max H, (1 - if a ∈ M.1 then (1 : ℝ) else 0)) =
      if Subgroup.zpowers a = ⊤ then 1 else 0 := by
    simp only [show ∀ M : Max H, (1 - if a ∈ M.1 then (1 : ℝ) else 0) =
        if a ∉ M.1 then 1 else 0 by intro M; split_ifs <;> simp_all,
      Fintype.prod_boole, ← zpowers_eq_top_iff_forall_not_mem_max]
  rw [← hprod, Finset.prod_sub]
  simp [Finset.prod_boole, D, Subgroup.mem_iInf]

/-- Averaging the maximal-subgroup inclusion-exclusion formula in a finite cyclic
group gives the proportion of generators. -/
theorem generator_density_coefficient [IsCyclic H] :
    (∑ J ∈ (Finset.univ : Finset (Max H)).powerset,
      (-1 : ℝ) ^ J.card * (Nat.card (D H J) : ℝ) / Nat.card H) =
        (Nat.totient (Nat.card H) : ℝ) / Nat.card H := by
  classical
  let := Fintype.ofFinite H
  have hcount : (∑ a : H, if Subgroup.zpowers a = ⊤ then (1 : ℝ) else 0) =
      Nat.totient (Nat.card H) := by
    simp only [← Subgroup.card_eq_iff_eq_top, Nat.card_zpowers]
    simp only [Nat.card_eq_fintype_card]
    rw [Finset.sum_boole, IsCyclic.card_orderOf_eq_totient dvd_rfl]
  have hsub (J : Finset (Max H)) :
      (∑ a : H, if a ∈ D H J then (1 : ℝ) else 0) = Nat.card (D H J) := by
    rw [Finset.sum_boole, ← Fintype.card_subtype, Nat.card_eq_fintype_card]
  rw [← Finset.sum_div, ← hcount]
  congr 1
  simp_rw [generator_indicator]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [← Finset.mul_sum, hsub]

end Chebotarev
