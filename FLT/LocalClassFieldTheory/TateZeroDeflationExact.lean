/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.TateZeroDeflation
public import FLT.LocalClassFieldTheory.TateZeroTransfer

/-!
# Exactness of norm-quotient deflation

For a normal subgroup, the kernel of deflation is exactly the image of
subgroup corestriction. This uses the actual quotient norm, without cancelling
the subgroup order.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

variable {k G : Type} [CommRing k] [Group G] [Fintype G]
  (M : Rep k G) (N : Subgroup G) [N.Normal] [Fintype N] [Fintype (G ⧸ N)]

local notation "MN" => Rep.res N.subtype M
local notation "MQ" => M.quotientToInvariants N

omit [Fintype G] [Fintype N] in
/-- On subgroup invariants, coset transfer is the quotient norm. -/
theorem quotientNorm_transferInvariant (x : (MN).ρ.invariants) :
    (MQ).norm.hom x = (quotientInvariantEquiv M N (transferInvariant M N x)).val := by
  classical
  apply Subtype.ext
  change (((∑ q : G ⧸ N, (MQ).ρ q) x : MQ) : M) = transferZero M N x
  rw [LinearMap.sum_apply, Submodule.coe_sum, transferZero_apply]
  apply Finset.sum_congr rfl
  intro q _
  conv_lhs => rw [← QuotientGroup.out_eq' q]
  rfl

/-- Deflation kills every class corestricted from the normal subgroup. -/
theorem tateZeroDeflation_corestriction (x : tateCohomology MN 0) :
    tateZeroDeflation M N (tateZeroCorestriction M N x) = 0 := by
  obtain ⟨y, rfl⟩ := tateInvariantClass_surjective MN x
  rw [tateZeroCorestriction_class, tateZeroDeflation_class]
  exact (tateInvariantClass_eq_zero_iff MQ _).mpr
    ⟨y, quotientNorm_transferInvariant M N y⟩

/-- A class deflates to zero exactly when it is a subgroup corestriction. -/
theorem tateZeroDeflation_eq_zero_iff (x : tateCohomology M 0) :
    tateZeroDeflation M N x = 0 ↔
      ∃ y : tateCohomology MN 0, tateZeroCorestriction M N y = x := by
  constructor
  · obtain ⟨a, rfl⟩ := tateInvariantClass_surjective M x
    intro hx
    obtain ⟨y, hy⟩ := (tateZeroDeflation_class_eq_zero_iff M N a).mp hx
    refine ⟨tateInvariantClass MN y, ?_⟩
    rw [tateZeroCorestriction_class]
    apply congrArg (tateInvariantClass M)
    apply (quotientInvariantEquiv M N).injective
    exact Subtype.ext ((quotientNorm_transferInvariant M N y).symm.trans hy)
  · rintro ⟨y, rfl⟩
    exact tateZeroDeflation_corestriction M N y

end LocalClassFieldTheory
