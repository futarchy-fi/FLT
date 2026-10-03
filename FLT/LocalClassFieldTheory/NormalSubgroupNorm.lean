/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.SubgroupNormDecomposition
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# Normal subgroup norm and degree-one descent

The subgroup norm commutes with the full group action. Degree-one vanishing
descends to the quotient by the injective inflation map.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology

variable {k G : Type} [CommRing k] [Group G] (M : Rep k G)
  (N : Subgroup G) [N.Normal]

/-- Injective inflation descends degree-one vanishing to normal-subgroup invariants. -/
theorem quotientInvariant_H1_isZero (h₁ : Limits.IsZero (groupCohomology M 1)) :
    Limits.IsZero (groupCohomology (M.quotientToInvariants N) 1) :=
  Limits.IsZero.of_mono (H1InfRes M N).f h₁

section Tate

variable [Fintype G] [Fintype (G ⧸ N)]

/-- The degree-one Tate form of injective inflation. -/
theorem quotientInvariant_tate_one_isZero (h₁ : Limits.IsZero (tateCohomology M 1)) :
    Limits.IsZero (tateCohomology (M.quotientToInvariants N) 1) := by
  have h := h₁.of_iso ((TateCohomology.isoGroupCohomology 1).app M).symm
  exact (quotientInvariant_H1_isZero M N h).of_iso
    ((TateCohomology.isoGroupCohomology 1).app (M.quotientToInvariants N))

end Tate

section Norm

variable [Fintype N]

/-- Normality makes the subgroup norm equivariant for the ambient group. -/
theorem subgroupNorm_action (g : G) (x : M) :
    (Rep.res N.subtype M).norm.hom (M.ρ g x) =
      M.ρ g ((Rep.res N.subtype M).norm.hom x) := by
  classical
  change (∑ n : N, M.ρ n) (M.ρ g x) = M.ρ g ((∑ n : N, M.ρ n) x)
  simp only [LinearMap.sum_apply, map_sum]
  apply Fintype.sum_equiv (MulAut.conjNormal g⁻¹ : MulAut N).toEquiv
  intro n
  simp only [← Module.End.mul_apply, ← map_mul]
  congr 2
  simp [mul_assoc]

/-- The invariant-valued subgroup norm is equivariant for the quotient action. -/
theorem subgroupNormInvariant_action (g : G) (x : M) :
    subgroupNormInvariant M N (M.ρ g x) =
      (M.quotientToInvariants N).ρ (QuotientGroup.mk' N g)
        (subgroupNormInvariant M N x) :=
  Subtype.ext (subgroupNorm_action M N g x)

/-- Degree-zero vanishing on the subgroup makes its invariant-valued norm surjective. -/
theorem subgroupNormInvariant_surjective
    (h₀ : Limits.IsZero (tateCohomology (Rep.res N.subtype M) 0)) :
    Function.Surjective (subgroupNormInvariant M N) := by
  intro x
  obtain ⟨y, hy⟩ := norm_surjective_of_tate_zero (Rep.res N.subtype M) h₀ x (by
    ext n
    exact sub_eq_zero.mpr (x.property n))
  exact ⟨y, Subtype.ext hy⟩

end Norm

end LocalClassFieldTheory
