/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.OneCocycleInvariantSequence
public import FLT.LocalClassFieldTheory.TateBoundaryLowDegree

/-!
# The first divided invariant boundary

The subgroup norm of `(0,1)` lifts the quotient scalar generator. Its action
difference is the subgroup norm of the original cocycle value.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology groupHomology

variable {G : Type} [Group G] (Q : Rep.{0} ℤ G) (b : cocycles₁ Q)
  (N : Subgroup G) [N.Normal] [Fintype N] [Fintype (G ⧸ N)]
  (h₀ : Limits.IsZero (tateCohomology (Rep.res N.subtype (oneCocycleExtension Q b)) 0))

local notation "X" => oneCocycleExtension Q b
local notation "QQ" => Rep.quotientToInvariants Q N
local notation "XQ" => Rep.quotientToInvariants X N
local notation "D" => oneCocycleInvariantSequence Q b N h₀
local notation "q" => QuotientGroup.mk' N

omit [Fintype (G ⧸ N)] in
/-- Subgroup norms commute with every equivariant coefficient map. -/
theorem subgroupNormInvariant_map {A B : Rep ℤ G} (f : A ⟶ B) (x : A) :
    (CategoryTheory.Functor.map (Rep.quotientToInvariantsFunctor ℤ N) f).hom
      (subgroupNormInvariant A N x) = subgroupNormInvariant B N (f.hom x) := by
  apply Subtype.ext
  have h := congrArg (fun t => t.hom x)
    (Rep.norm_comm ((Rep.resFunctor N.subtype).map f))
  exact h.symm

omit [Fintype (G ⧸ N)] in
/-- The action difference of the normed scalar lift is the normed cocycle value. -/
theorem invariant_scalarLift_difference (g : G) :
    (D).f.hom (subgroupNormInvariant Q N (b g⁻¹)) =
      (XQ).ρ (q g)⁻¹ (subgroupNormInvariant X N (0, (1 : ℤ))) -
        subgroupNormInvariant X N (0, (1 : ℤ)) := by
  change (CategoryTheory.Functor.map (Rep.quotientToInvariantsFunctor ℤ N)
    (oneCocycleInclusion Q b)).hom _ = _
  rw [subgroupNormInvariant_map, ← map_inv, ← subgroupNormInvariant_action]
  apply Subtype.ext
  change (Rep.res N.subtype X).norm.hom ((oneCocycleInclusion Q b).hom (b g⁻¹)) =
    (Rep.res N.subtype X).norm.hom ((X).ρ g⁻¹ (0, (1 : ℤ))) -
      (Rep.res N.subtype X).norm.hom (0, (1 : ℤ))
  rw [← map_sub]
  congr 1
  exact congrFun (oneCocycle_lift_d Q b) g⁻¹

/-- The divided invariant boundary has an explicit subgroup-norm representative. -/
theorem oneCocycleInvariant_negative_boundary (g : G) :
    ∃ hz, TateCohomology.δ (oneCocycleInvariantSequence_shortExact Q b N h₀) (-2)
      (tateScalarGenerator ℤ (G ⧸ N) (q g)) =
      tateCocycleClass QQ (-1)
        ((chainsIso₀ QQ).inv (subgroupNormInvariant Q N (b g⁻¹))) hz := by
  exact tate_boundary_negative_two D (oneCocycleInvariantSequence_shortExact Q b N h₀)
    (q g) (1 : ℤ) (tateScalarGenerator_cycle ℤ (G ⧸ N) (q g))
    (subgroupNormInvariant X N (0, (1 : ℤ)))
    (oneCocycleInvariantProjection_norm Q b N h₀ 1)
    (subgroupNormInvariant Q N (b g⁻¹)) (invariant_scalarLift_difference Q b N h₀ g)

end LocalClassFieldTheory
