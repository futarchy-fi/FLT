/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.SubgroupTransferNorm

/-!
# Right-coset decomposition of the Tate norm

Inverting left-coset coordinates gives a decomposition with the subgroup norm
last. This is the norm-splice identity required for Tate restriction.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

variable {k G : Type} [CommRing k] [Group G]
  (M : Rep k G) (H : Subgroup G) [Fintype (G ⧸ H)]

/-- The negative-side degree-zero coefficient map for restriction. -/
def restrictionZero : M →ₗ[k] M := ∑ q : G ⧸ H, M.ρ q.out⁻¹

/-- Restriction at the norm splice is the sum of inverse-representative actions. -/
theorem restrictionZero_apply (x : M) :
    restrictionZero M H x = ∑ q : G ⧸ H, M.ρ q.out⁻¹ x := by
  classical
  exact LinearMap.sum_apply _ _ _

/-- Restriction of invariant coefficients along subgroup inclusion. -/
def restrictInvariant : M.ρ.invariants →ₗ[k] (Rep.res H.subtype M).ρ.invariants :=
  M.ρ.invariants.subtype.codRestrict _ fun x h => x.property h

variable [Fintype G] [Fintype H]

/-- Inverted left-coset coordinates give the full norm as a subgroup norm. -/
theorem norm_sum_right_cosets (x : M) :
    (Rep.res H.subtype M).norm.hom (restrictionZero M H x) = M.norm.hom x := by
  classical
  change (∑ h : H, M.ρ h) (restrictionZero M H x) = (∑ g : G, M.ρ g) x
  simp only [LinearMap.sum_apply, restrictionZero_apply, map_sum]
  calc
    _ = ∑ q : G ⧸ H, ∑ h : H, M.ρ (h⁻¹ * q.out⁻¹) x := by
      apply Finset.sum_congr rfl
      intro q _
      rw [← Equiv.sum_comp (Equiv.inv H) (fun h : H => M.ρ h (M.ρ q.out⁻¹ x))]
      apply Finset.sum_congr rfl
      intro h _
      change M.ρ (h⁻¹ : H) (M.ρ q.out⁻¹ x) = _
      rw [map_mul]
      rfl
    _ = ∑ g : G, M.ρ g x := by
      have he := ((normCosetEquiv H).trans (Equiv.inv G)).sum_comp (fun g => M.ρ g x)
      simpa [Fintype.sum_prod_type, normCosetEquiv, mul_inv_rev] using he

omit [Fintype G] [Fintype H] in
/-- Transfer after restriction acts on invariants by the subgroup index. -/
theorem transferInvariant_restrictInvariant (x : M.ρ.invariants) :
    transferInvariant M H (restrictInvariant M H x) = Fintype.card (G ⧸ H) • x := by
  apply Subtype.ext
  exact transferZero_of_invariant M H x

end LocalClassFieldTheory
