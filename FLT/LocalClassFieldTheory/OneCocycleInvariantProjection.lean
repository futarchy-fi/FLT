/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.OneCocycleExtension
public import FLT.LocalClassFieldTheory.NormalSubgroupNorm

/-!
# Dividing the invariant extension projection

If the twisted extension has vanishing subgroup Tate H⁰, its invariant
projection has image exactly the subgroup-order multiples in ℤ. Dividing
this projection constructs the quotient extension's surjection onto ℤ.
The division is performed in ℤ, not in a torsion cohomology group.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology

variable {G : Type} [Group G] (Q : Rep.{0} ℤ G) (b : cocycles₁ Q)
  (N : Subgroup G) [N.Normal] [Fintype N]

local notation "X" => oneCocycleExtension Q b
local notation "XN" => Rep.res N.subtype X
local notation "XQ" => Rep.quotientToInvariants X N
local notation "m" => (Fintype.card N : ℤ)

/-- Use the representation's integral module structure on its invariant coefficients. -/
local instance oneCocycleInvariantModule :
    Module ℤ ((oneCocycleExtension Q b).quotientToInvariants N) :=
  ((oneCocycleExtension Q b).quotientToInvariants N).hV2

omit [N.Normal] in
/-- The subgroup norm multiplies the scalar projection by the subgroup order. -/
theorem oneCocycle_subgroupNorm_snd (x : X) :
    ((XN).norm.hom x).2 = m * x.2 := by
  have hn := congrArg (fun f => f.hom x)
    (Rep.norm_comm ((Rep.resFunctor N.subtype).map (oneCocycleProjection Q b)))
  change (Rep.trivial ℤ N ℤ).norm.hom x.2 = ((XN).norm.hom x).2 at hn
  rw [← hn]
  simp [Rep.norm, Representation.norm]

variable (h₀ : Limits.IsZero
  (tateCohomology (Rep.res N.subtype (oneCocycleExtension Q b)) 0))

include h₀ in
/-- Every subgroup-invariant scalar projection is divisible by the subgroup order. -/
theorem oneCocycle_invariant_snd_dvd (x : XQ) : m ∣ x.val.2 := by
  obtain ⟨y, hy⟩ := subgroupNormInvariant_surjective X N h₀ x
  refine ⟨y.2, ?_⟩
  have hs := congrArg (fun z : XQ => z.val.2) hy
  exact hs.symm.trans (oneCocycle_subgroupNorm_snd Q b N y)

/-- The divided scalar coordinate is an integral linear map. -/
def oneCocycleInvariantProjectionLinear : XQ →ₗ[ℤ] ℤ where
    toFun x := x.val.2 / m
    map_add' x y := by
      apply mul_right_cancel₀ (show m ≠ 0 from Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
      rw [add_mul, Int.ediv_mul_cancel (oneCocycle_invariant_snd_dvd Q b N h₀ x),
        Int.ediv_mul_cancel (oneCocycle_invariant_snd_dvd Q b N h₀ y)]
      exact Int.ediv_mul_cancel (oneCocycle_invariant_snd_dvd Q b N h₀ (x + y))
    map_smul' r x := by
      change (r • x).val.2 / m = r * (x.val.2 / m)
      apply mul_right_cancel₀ (show m ≠ 0 from Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
      rw [mul_assoc, Int.ediv_mul_cancel (oneCocycle_invariant_snd_dvd Q b N h₀ x)]
      exact Int.ediv_mul_cancel (oneCocycle_invariant_snd_dvd Q b N h₀ (r • x))

/-- The divided projection on the actual invariant extension. -/
def oneCocycleInvariantProjection : XQ ⟶ Rep.trivial ℤ (G ⧸ N) ℤ :=
  ConcreteCategory.ofHom (C := Rep ℤ (G ⧸ N))
    ⟨oneCocycleInvariantProjectionLinear Q b N h₀, fun g => by
    apply LinearMap.ext
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N g
    rfl⟩

/-- Multiplying the divided projection recovers the original scalar coordinate. -/
theorem oneCocycleInvariantProjection_mul (x : XQ) :
    (oneCocycleInvariantProjection Q b N h₀).hom x * m = x.val.2 :=
  Int.ediv_mul_cancel (oneCocycle_invariant_snd_dvd Q b N h₀ x)

/-- A subgroup norm of the scalar lift maps to that scalar under the divided projection. -/
theorem oneCocycleInvariantProjection_norm (z : ℤ) :
    (oneCocycleInvariantProjection Q b N h₀).hom
      (subgroupNormInvariant X N (0, z)) = z := by
  change ((XN).norm.hom (0, z)).2 / m = z
  rw [oneCocycle_subgroupNorm_snd]
  exact Int.mul_ediv_cancel_left z (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

/-- The divided invariant projection is surjective, with explicit norm lifts. -/
theorem oneCocycleInvariantProjection_surjective :
    Function.Surjective (oneCocycleInvariantProjection Q b N h₀).hom :=
  fun z => ⟨subgroupNormInvariant X N (0, z), oneCocycleInvariantProjection_norm Q b N h₀ z⟩

end LocalClassFieldTheory
