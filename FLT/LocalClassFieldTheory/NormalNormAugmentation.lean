/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.NormalSubgroupNorm

/-!
# Augmentation under a normal subgroup norm

A surjective subgroup norm maps the ambient augmentation submodule onto the
quotient augmentation submodule. This supplies the norm-splice descent step.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupHomology Representation

variable {k G : Type} [CommRing k] [Group G] (M : Rep k G)
  (N : Subgroup G) [N.Normal] [Fintype N]

/-- The invariant-valued subgroup norm as a linear map. -/
def subgroupNormLinear : M →ₗ[k] M.quotientToInvariants N :=
  (Rep.res N.subtype M).norm.hom.toLinearMap.codRestrict _
    (fun x => (subgroupNormInvariant M N x).property)

omit [N.Normal] [Fintype N] in
/-- Subgroup augmentation is contained in ambient augmentation. -/
theorem subgroup_augmentation_le :
    Coinvariants.ker (Rep.res N.subtype M).ρ ≤ Coinvariants.ker M.ρ := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨n, x⟩, rfl⟩
  exact Coinvariants.sub_mem_ker (n : G) x

/-- The subgroup norm sends ambient augmentation into quotient augmentation. -/
theorem subgroupNorm_augmentation_le :
    (Coinvariants.ker M.ρ).map (subgroupNormLinear M N) ≤
      Coinvariants.ker (M.quotientToInvariants N).ρ := by
  rw [Submodule.map_le_iff_le_comap]
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨g, x⟩, rfl⟩
  change subgroupNormLinear M N (M.ρ g x - x) ∈
    Coinvariants.ker (M.quotientToInvariants N).ρ
  rw [map_sub]
  change subgroupNormInvariant M N (M.ρ g x) - subgroupNormInvariant M N x ∈
    Coinvariants.ker (M.quotientToInvariants N).ρ
  rw [subgroupNormInvariant_action]
  exact Coinvariants.sub_mem_ker (QuotientGroup.mk' N g) _

/-- Surjectivity of the subgroup norm gives equality of augmentation images. -/
theorem subgroupNorm_augmentation_eq
    (h₀ : Limits.IsZero (tateCohomology (Rep.res N.subtype M) 0)) :
    (Coinvariants.ker M.ρ).map (subgroupNormLinear M N) =
      Coinvariants.ker (M.quotientToInvariants N).ρ := by
  apply le_antisymm (subgroupNorm_augmentation_le M N)
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨q, y⟩, rfl⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
  obtain ⟨x, rfl⟩ := subgroupNormInvariant_surjective M N h₀ y
  refine ⟨M.ρ g x - x, Coinvariants.sub_mem_ker g x, ?_⟩
  rw [map_sub]
  exact congrArg (· - subgroupNormInvariant M N x) (subgroupNormInvariant_action M N g x)

omit [N.Normal] [Fintype N] in
/-- Degree minus one vanishing identifies the norm kernel with augmentation. -/
theorem norm_kernel_mem_augmentation [Fintype G]
    (h : Limits.IsZero (tateCohomology M (-1))) (x : M) (hx : M.norm.hom x = 0) :
    x ∈ Coinvariants.ker M.ρ := by
  rw [← range_d₁₀_eq_coinvariantsKer M]
  exact augmentation_exact_of_tate_neg_one M h x hx

omit [N.Normal] [Fintype N] in
/-- Augmentation-kernel containment implies degree minus one vanishing. -/
theorem tate_neg_one_isZero_of_norm_kernel [Fintype G]
    (h : ∀ x : M, M.norm.hom x = 0 → x ∈ Coinvariants.ker M.ρ) :
    Limits.IsZero (tateCohomology M (-1)) := by
  apply tate_neg_one_isZero_of_augmentation_exact
  intro x hx
  have hm : x ∈ LinearMap.range (d₁₀ M).hom := by
    rw [range_d₁₀_eq_coinvariantsKer]
    exact h x hx
  exact hm

end LocalClassFieldTheory
