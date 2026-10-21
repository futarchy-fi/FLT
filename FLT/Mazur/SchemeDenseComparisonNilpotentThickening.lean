/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealSheafSupportPower
public import FLT.Mazur.SchemeFiniteComparisonDenseTests

/-!
# The entire finite comparison kernel is a nilpotent ideal sheaf

On Noetherian coefficient schemes dense comparison coverage yields one power
annihilating the full comparison-test kernel. This is stronger than separate
nilpotence exponents for individual equations and does not assert kernel zero.
The original boundary and its ideals are unchanged.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeFiniteEndpointComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- A surjective map into a Noetherian scheme has a uniformly nilpotent schematic kernel. -/
theorem surjective_kernel_isNilpotent {X Y : Scheme.{0}} [IsNoetherian Y]
    (i : X ⟶ Y) [QuasiCompact i] [Surjective i] : IsNilpotent i.ker := by
  have hs : (⊥ : Y.IdealSheafData).support ≤ i.ker.support := by
    rw [← SetLike.coe_subset_coe, Scheme.Hom.support_ker]
    rw [Set.range_eq_univ.mpr i.surjective, closure_univ]
    exact Set.subset_univ _
  obtain ⟨n, hn⟩ := IdealSheafSupportPower.exists_pow_le_of_support i.ker ⊥ hs
  exact ⟨n + 1, le_antisymm hn bot_le⟩

variable {D T B : Scheme.{0}} (c : D ⟶ T) (b : B ⟶ T)
  [IsFinite (pullback.snd c b)] [IsNoetherian B]

/-- Dense coverage constructs a full nilpotent comparison thickening, without reduction. -/
theorem comparison_kernel_sheaf_isNilpotent_of_dense
    (h : Dense (b ⁻¹' Set.range c)) : IsNilpotent (pullback.snd c b).ker := by
  let _ := comparison_surjective_of_dense c b h
  exact surjective_kernel_isNilpotent (pullback.snd c b)

/-- One positive power kills every local equation of the actual comparison test at once. -/
theorem comparison_kernel_sheaf_pow_of_dense
    (h : Dense (b ⁻¹' Set.range c)) :
    ∃ n : ℕ, (pullback.snd c b).ker ^ (n + 1) = ⊥ := by
  obtain ⟨n, hn⟩ := comparison_kernel_sheaf_isNilpotent_of_dense c b h
  refine ⟨n, ?_⟩
  rw [pow_succ, hn, zero_mul]
  rfl

end FLT.Mazur.SchemeFiniteEndpointComparison
