/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.TateNormVanishing
public import Mathlib.GroupTheory.Coset.Basic

/-!
# Subgroup norms and quotient norms

The full norm is the sum over left coset representatives of the subgroup norm.
For a normal subgroup this is the norm of the quotient acting on invariants.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology

variable {k G : Type} [CommRing k] [Group G] [Fintype G]
  (M : Rep k G) (N : Subgroup G) [Fintype N] [Fintype (G ⧸ N)]

/-- Explicit left-coset coordinates with chosen representatives. -/
def normCosetEquiv : (G ⧸ N) × N ≃ G where
  toFun qn := qn.1.out * qn.2
  invFun g := ⟨QuotientGroup.mk g, ⟨(QuotientGroup.mk g : G ⧸ N).out⁻¹ * g, by
    apply QuotientGroup.eq.mp
    exact QuotientGroup.out_eq' _⟩⟩
  left_inv := by
    rintro ⟨q, n⟩
    have hq : (QuotientGroup.mk (q.out * n) : G ⧸ N) = q := by
      rw [QuotientGroup.mk_mul_of_mem _ n.property, QuotientGroup.out_eq']
    apply Prod.ext hq
    apply Subtype.ext
    simp [hq]
  right_inv g := by simp

/-- Expanding the norm along left cosets gives the subgroup norm first. -/
theorem norm_sum_cosets (x : M) :
    M.norm.hom x = ∑ q : G ⧸ N, M.ρ q.out ((Rep.res N.subtype M).norm.hom x) := by
  classical
  change (∑ g : G, M.ρ g) x = ∑ q : G ⧸ N, M.ρ q.out ((∑ n : N, M.ρ n) x)
  simp only [LinearMap.sum_apply, map_sum]
  rw [← (normCosetEquiv N).sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro n _
  change M.ρ (q.out * n) x = M.ρ q.out (M.ρ n x)
  simp

variable [N.Normal]

/-- The subgroup norm takes values in the invariant submodule. -/
def subgroupNormInvariant (x : M) : M.quotientToInvariants N :=
  ⟨(Rep.res N.subtype M).norm.hom x,
    fun n => (Rep.res N.subtype M).ρ.self_norm_apply n x⟩

/-- Taking the quotient norm of the subgroup norm gives the full norm. -/
theorem quotientNorm_subgroupNorm (x : M) :
    ((M.quotientToInvariants N).norm.hom (subgroupNormInvariant M N x) : M) =
      M.norm.hom x := by
  rw [norm_sum_cosets M N x]
  change (((∑ q : G ⧸ N, (M.quotientToInvariants N).ρ q)
    (subgroupNormInvariant M N x) : M.quotientToInvariants N) : M) = _
  rw [LinearMap.sum_apply, Submodule.coe_sum]
  apply Finset.sum_congr rfl
  intro q _
  conv_lhs => rw [← QuotientGroup.out_eq' q]
  rfl

omit [Fintype N] in
/-- Degree-zero vanishing descends to the quotient acting on subgroup invariants. -/
theorem quotientInvariant_tate_zero_isZero
    (h₀ : Limits.IsZero (tateCohomology M 0)) :
    Limits.IsZero (tateCohomology (M.quotientToInvariants N) 0) := by
  classical
  let : Fintype N := Fintype.ofFinite N
  apply tate_zero_isZero_of_norm_surjective
  intro x hx
  have hfixed : d₀₁ M (x : M) = 0 := by
    ext g
    have hg := congrFun hx (QuotientGroup.mk' N g)
    exact congrArg Subtype.val hg
  obtain ⟨y, hy⟩ := norm_surjective_of_tate_zero M h₀ x hfixed
  exact ⟨subgroupNormInvariant M N y, Subtype.ext
    ((quotientNorm_subgroupNorm M N y).trans hy)⟩

end LocalClassFieldTheory
