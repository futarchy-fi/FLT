/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.CyclicTateSplice
public import FLT.LocalClassFieldTheory.NormalTateSplice
public import FLT.LocalClassFieldTheory.SolvableCyclicQuotient
public import FLT.LocalClassFieldTheory.SubgroupTateVanishing

/-!
# Adjacent vanishing across the solvable norm splice

Induction on the group order, with a cyclic quotient, passes between the
pairs of Tate degrees `(0, 1)` and `(-1, 0)` on all subgroups.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology

variable {k G : Type} [CommRing k] [Group G] [Fintype G] [Group.IsSolvable G]
  (M : Rep k G)

/-- Adjacent subgroup vanishing gives degree minus one for a finite solvable group. -/
theorem solvable_tate_neg_one_isZero
    (h₀ : SubgroupTateVanishing M 0) (h₁ : SubgroupTateVanishing M 1) :
    Limits.IsZero (tateCohomology M (-1)) := by
  classical
  induction hn : Nat.card G using Nat.strong_induction_on generalizing G with
  | h n ih =>
    by_cases hc : IsCyclic G
    · let := hc
      exact cyclic_tate_isZero_of_adjacent M h₀.self h₁.self (-1)
    · have : Nontrivial G := by
        by_contra h
        have := not_nontrivial_iff_subsingleton.mp h
        exact hc inferInstance
      obtain ⟨N, hN, htop, hQ⟩ := solvable_cyclic_quotient G
      let := hN
      let := hQ
      let : Fintype N := Fintype.ofFinite N
      let : Fintype (G ⧸ N) := Fintype.ofFinite _
      have hlt : Nat.card N < n := by
        rw [← hn]
        exact lt_of_le_of_ne N.card_le_card_group (fun h => htop (N.eq_top_of_card_eq h))
      apply tate_neg_one_isZero_of_normal_subgroup M N (h₀ N)
      · exact ih (Nat.card N) hlt (Rep.res N.subtype M) (h₀.res N) (h₁.res N) rfl
      · exact cyclic_tate_isZero_of_adjacent (M.quotientToInvariants N)
          (quotientInvariant_tate_zero_isZero M N h₀.self)
          (quotientInvariant_tate_one_isZero M N h₁.self) (-1)

omit [Group.IsSolvable G] in
/-- Vanishing at the subgroup and quotient in degree one gives ambient vanishing. -/
theorem tate_one_isZero_of_normal_subgroup (N : Subgroup G) [N.Normal]
    [Fintype N] [Fintype (G ⧸ N)]
    (hN : Limits.IsZero (tateCohomology (Rep.res N.subtype M) 1))
    (hQ : Limits.IsZero (tateCohomology (M.quotientToInvariants N) 1)) :
    Limits.IsZero (tateCohomology M 1) := by
  have hN' := hN.of_iso ((TateCohomology.isoGroupCohomology 1).app (Rep.res N.subtype M)).symm
  have hQ' := hQ.of_iso
    ((TateCohomology.isoGroupCohomology 1).app (M.quotientToInvariants N)).symm
  exact ((H1InfRes_exact M N).isZero_X₂ (hQ'.eq_of_src _ 0) (hN'.eq_of_tgt _ 0)).of_iso
    ((TateCohomology.isoGroupCohomology 1).app M)

/-- Vanishing on the norm splice gives degree one for a finite solvable group. -/
theorem solvable_tate_one_isZero
    (hm : SubgroupTateVanishing M (-1)) (h₀ : SubgroupTateVanishing M 0) :
    Limits.IsZero (tateCohomology M 1) := by
  classical
  induction hn : Nat.card G using Nat.strong_induction_on generalizing G with
  | h n ih =>
    by_cases hc : IsCyclic G
    · let := hc
      exact cyclic_tate_one_isZero_of_neg_one M hm.self
    · have : Nontrivial G := by
        by_contra h
        have := not_nontrivial_iff_subsingleton.mp h
        exact hc inferInstance
      obtain ⟨N, hN, htop, hQ⟩ := solvable_cyclic_quotient G
      let := hN
      let := hQ
      let : Fintype N := Fintype.ofFinite N
      let : Fintype (G ⧸ N) := Fintype.ofFinite _
      have hlt : Nat.card N < n := by
        rw [← hn]
        exact lt_of_le_of_ne N.card_le_card_group (fun h => htop (N.eq_top_of_card_eq h))
      apply tate_one_isZero_of_normal_subgroup M N
      · exact ih (Nat.card N) hlt (Rep.res N.subtype M) (hm.res N) (h₀.res N) rfl
      · exact cyclic_tate_one_isZero_of_neg_one (M.quotientToInvariants N)
          (quotientInvariant_tate_neg_one_isZero M N (h₀ N) hm.self)

end LocalClassFieldTheory
