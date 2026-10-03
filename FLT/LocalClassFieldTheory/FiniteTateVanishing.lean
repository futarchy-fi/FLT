/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.SolvableTateVanishing
public import FLT.LocalClassFieldTheory.SylowTateDetection
public import Mathlib.GroupTheory.Nilpotent

/-!
# Adjacent vanishing for arbitrary finite groups

Finite Sylow groups are nilpotent and hence solvable. Apply the proved
solvable criterion to each Sylow subgroup and then all-degree Sylow detection.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open CategoryTheory

variable {k G : Type} [CommRing k] [Group G] [Fintype G] (M : Rep k G)

/-- Adjacent vanishing on all subgroups implies Tate acyclicity for any finite group. -/
theorem finite_tate_isZero_of_adjacent
    (h₀ : SubgroupTateVanishing M 0) (h₁ : SubgroupTateVanishing M 1) (n : ℤ) :
    Limits.IsZero (tateCohomology M n) := by
  apply tate_isZero_of_sylow M _ n
  intro i p _ P _
  let : Group.IsNilpotent P := P.isPGroup'.isNilpotent
  exact solvable_tate_isZero_of_adjacent (Rep.res (P : Subgroup G).subtype M)
    (h₀.res P) (h₁.res P) i

omit [Fintype G] in
/-- The finite criterion also supplies all-degree vanishing on every subgroup. -/
theorem finite_subgroup_tate_isZero_of_adjacent
    (h₀ : SubgroupTateVanishing M 0) (h₁ : SubgroupTateVanishing M 1) (n : ℤ) :
    SubgroupTateVanishing M n := by
  intro H _
  exact finite_tate_isZero_of_adjacent (Rep.res H.subtype M) (h₀.res H) (h₁.res H) n

end LocalClassFieldTheory
