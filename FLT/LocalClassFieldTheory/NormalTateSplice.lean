/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.NormalNormAugmentation

/-!
# Descent and ascent at the Tate norm splice

When the subgroup norm is surjective, degree minus one vanishing descends to
the quotient. If the subgroup also has zero degree minus one, quotient
vanishing ascends to the full group.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory Representation

variable {k G : Type} [CommRing k] [Group G] [Fintype G] (M : Rep k G)
  (N : Subgroup G) [N.Normal] [Fintype N] [Fintype (G ⧸ N)]

/-- Vanishing at minus one descends through a surjective subgroup norm. -/
theorem quotientInvariant_tate_neg_one_isZero
    (h₀ : Limits.IsZero (tateCohomology (Rep.res N.subtype M) 0))
    (h : Limits.IsZero (tateCohomology M (-1))) :
    Limits.IsZero (tateCohomology (M.quotientToInvariants N) (-1)) := by
  apply tate_neg_one_isZero_of_norm_kernel
  intro y hy
  obtain ⟨x, rfl⟩ := subgroupNormInvariant_surjective M N h₀ y
  have hx : M.norm.hom x = 0 := by
    rw [← quotientNorm_subgroupNorm M N]
    exact congrArg Subtype.val hy
  apply subgroupNorm_augmentation_le M N
  exact ⟨x, norm_kernel_mem_augmentation M h x hx, rfl⟩

/-- Vanishing at minus one ascends from subgroup and quotient. -/
theorem tate_neg_one_isZero_of_normal_subgroup
    (h₀ : Limits.IsZero (tateCohomology (Rep.res N.subtype M) 0))
    (hN : Limits.IsZero (tateCohomology (Rep.res N.subtype M) (-1)))
    (hQ : Limits.IsZero (tateCohomology (M.quotientToInvariants N) (-1))) :
    Limits.IsZero (tateCohomology M (-1)) := by
  apply tate_neg_one_isZero_of_norm_kernel
  intro x hx
  have hy : (M.quotientToInvariants N).norm.hom (subgroupNormInvariant M N x) = 0 :=
    Subtype.ext ((quotientNorm_subgroupNorm M N x).trans hx)
  have hm := norm_kernel_mem_augmentation (M.quotientToInvariants N) hQ _ hy
  rw [← subgroupNorm_augmentation_eq M N h₀] at hm
  obtain ⟨z, hz, he⟩ := hm
  have hk : (Rep.res N.subtype M).norm.hom (x - z) = 0 := by
    rw [map_sub, sub_eq_zero]
    exact (congrArg Subtype.val he).symm
  have hd := subgroup_augmentation_le M N
    (norm_kernel_mem_augmentation (Rep.res N.subtype M) hN (x - z) hk)
  simpa only [sub_add_cancel] using (Coinvariants.ker M.ρ).add_mem hd hz

/-- With a vanishing subgroup norm splice, quotient and ambient minus one agree. -/
theorem quotientInvariant_tate_neg_one_iff
    (h₀ : Limits.IsZero (tateCohomology (Rep.res N.subtype M) 0))
    (hN : Limits.IsZero (tateCohomology (Rep.res N.subtype M) (-1))) :
    Limits.IsZero (tateCohomology (M.quotientToInvariants N) (-1)) ↔
      Limits.IsZero (tateCohomology M (-1)) :=
  ⟨tate_neg_one_isZero_of_normal_subgroup M N h₀ hN,
    quotientInvariant_tate_neg_one_isZero M N h₀⟩

end LocalClassFieldTheory
