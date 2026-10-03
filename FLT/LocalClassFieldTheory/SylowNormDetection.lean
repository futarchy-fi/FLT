/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.SubgroupNormDecomposition
public import Mathlib.GroupTheory.Sylow

/-!
# Detecting degree-zero Tate vanishing on Sylow subgroups

If an invariant is a subgroup norm, its index multiple is a full norm.
The Sylow indices have no common prime divisor, so their annihilation of the
norm-quotient class forces that class to vanish.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology

variable {k G : Type} [CommRing k] [Group G] [Fintype G] (M : Rep k G)

/-- An invariant subgroup norm has an index multiple which is a full norm. -/
theorem index_smul_mem_norm_range (H : Subgroup G) [Fintype H]
    (x : M) (hx : d₀₁ M x = 0)
    (hH : Limits.IsZero (tateCohomology (Rep.res H.subtype M) 0)) :
    H.index • x ∈ LinearMap.range M.norm.hom.toLinearMap := by
  classical
  let : Fintype (G ⧸ H) := Fintype.ofFinite _
  obtain ⟨y, hy⟩ := norm_surjective_of_tate_zero (Rep.res H.subtype M) hH x (by
    ext h
    exact congrFun hx (h : G))
  refine ⟨y, ?_⟩
  change M.norm.hom y = H.index • x
  rw [norm_sum_cosets M H, hy]
  have hf (g : G) : M.ρ g x = x := sub_eq_zero.mp (congrFun hx g)
  simp only [hf, Finset.sum_const, Finset.card_univ]
  rw [H.index_eq_card, Nat.card_eq_fintype_card]

/-- Vanishing in a Tate degree on all Sylow subgroups. -/
def SylowTateVanishing (n : ℤ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G) [Fintype P],
    Limits.IsZero (tateCohomology (Rep.res (P : Subgroup G).subtype M) n)

/-- Degree-zero Tate vanishing is detected on the Sylow subgroups. -/
theorem tate_zero_isZero_of_sylow (h : SylowTateVanishing M 0) :
    Limits.IsZero (tateCohomology M 0) := by
  classical
  apply tate_zero_isZero_of_norm_surjective
  intro x hx
  let U := LinearMap.range M.norm.hom.toLinearMap
  have hz : U.mkQ x = 0 := by
    by_contra hne
    have ho : addOrderOf (U.mkQ x) ≠ 1 := by
      intro he
      exact hne (AddMonoid.addOrderOf_eq_one_iff.mp he)
    obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd ho
    let : Fact p.Prime := ⟨hp⟩
    let P : Sylow p G := Classical.choice inferInstance
    let : Fintype P := Fintype.ofFinite P
    have hi : P.index • U.mkQ x = 0 := by
      rw [← map_nsmul]
      exact (Submodule.Quotient.mk_eq_zero U).mpr
        (index_smul_mem_norm_range M P x hx (h p P))
    exact P.not_dvd_index (hd.trans (addOrderOf_dvd_of_nsmul_eq_zero hi))
  exact (Submodule.Quotient.mk_eq_zero U).mp hz

end LocalClassFieldTheory
