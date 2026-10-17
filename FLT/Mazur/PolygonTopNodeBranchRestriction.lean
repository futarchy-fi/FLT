/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonTopNodeActionDefect

/-!
# Reconstructed higher node maps retain the preceding scaling

The full branch defect is killed by the original parameter. Separation of
both branches and flatness of the original node identify it with a top-layer
difference. Swapping branches preserves the same original coordinate algebra.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial PolygonScalingNaturality
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
variable (R : Type) [CommRing R] (m : ℕ)
local notation "S" => Ring R (m + 1)
local notation "e" => parameter R (m + 1)
local notation "B" => ChartRing (e)
local notation "β" => stageNodeBranchPair R (m + 1)
variable (u v : ((Ring R (m + 1))[T;T⁻¹])ˣ)
  (hx : stageNodeBranchLeftImage R (m + 1) u v ∈ stageNodeBranchSubalgebra R (m + 1))
  (hy : stageNodeBranchRightImage R (m + 1) u v ∈ stageNodeBranchSubalgebra R (m + 1))
  (a : (Ring R (m + 1))ˣ)
  (hu : coeffMap (restriction R m).toRingHom u.val = C (restriction R m a.val) * T 1)
  (hv : coeffMap (restriction R m).toRingHom v.val = C (restriction R m a⁻¹.val) * T 1)
include hu hv in
/-- The reconstructed whole node map has exactly its prescribed preceding-stage scaling. -/
theorem topNodeBranchReconstruct_restriction (z : B) :
    topNodeRestriction R m (stageNodeBranchReconstruct R (m + 1) u v hx hy z) =
      topNodeRestriction R m (reciprocalScale (e) a z) := by
  let d := stageNodeBranchReconstruct R (m + 1) u v hx hy z - reciprocalScale (e) a z
  have hd : (e) • d = 0 := by
    apply stageNodeBranchPair_injective R (m + 1)
    rw [map_smul, map_zero]
    change (e) • ((β) (_ - _)) = 0
    rw [map_sub, stageNodeBranchReconstruct_pair]
    exact topNodeActionDefect_parameter R m u v a hu hv z
  apply sub_eq_zero.mp
  rw [← (topNodeRestriction R m).map_sub]
  apply (topNodeRestriction_zero_iff R m d).mpr
  exact (flat_parameter_smul_eq_zero_iff R m (B) d).mp hd

/-- Interchanging branch factors retains the full higher node embedding. -/
theorem topNodeBranchPair_swap (z : B) :
    (β) (branchSwapMap (e) z) = ((β) z).swap := by
  apply Prod.ext
  · rfl
  · change leftLaurentMap (e) (branchSwapMap (e) (branchSwapMap (e) z)) = _
    exact congrArg (leftLaurentMap (e)) (AlgHom.congr_fun (branchSwapMap_comp (e)) z)

/-- Both retained coordinate rings survive swapping the original branches. -/
theorem topNodeBranchSubalgebra_swap (p : (S)[T;T⁻¹] × (S)[T;T⁻¹])
    (hp : p ∈ stageNodeBranchSubalgebra R (m + 1)) :
    p.swap ∈ stageNodeBranchSubalgebra R (m + 1) := by
  obtain ⟨z, rfl⟩ := hp
  exact ⟨branchSwapMap (e) z, topNodeBranchPair_swap R m z⟩

include hy in
/-- The original incoming coordinate supplies the opposite outgoing coordinate. -/
theorem topNodeBranchLeftImage_swap :
    stageNodeBranchLeftImage R (m + 1) v u ∈ stageNodeBranchSubalgebra R (m + 1) :=
  topNodeBranchSubalgebra_swap R m _ hy

include hx in
/-- The original outgoing coordinate supplies the opposite incoming coordinate. -/
theorem topNodeBranchRightImage_swap :
    stageNodeBranchRightImage R (m + 1) v u ∈ stageNodeBranchSubalgebra R (m + 1) :=
  topNodeBranchSubalgebra_swap R m _ hx

end FLT.Mazur.PolygonInfinitesimalStages
