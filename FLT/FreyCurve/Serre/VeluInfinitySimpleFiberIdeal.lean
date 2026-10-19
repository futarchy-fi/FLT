/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluInfinitySimpleNeighborhood

/-!
# Exact identity fiber ideal of the original Vélu map near infinity

The original target parameter pulls back to the original source parameter
times an explicit unit. Hence the entire target identity ideal pulls back
to the source identity ideal, without taking radicals.
-/

@[expose] public noncomputable section

open FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] infinitySimpleChart infinityTargetChart
  infinityTargetCoordinates infinitySimpleEvaluation infinityTargetEvaluation

variable {K : Type} [Field K] [CharZero K] [DecidableEq K]
  (E : WeierstrassCurve K) (G : AddSubgroup E.toAffine.Point) [Fintype G]

/-- The explicit multiplier relating the original target and source parameters. -/
def infinitySimpleMultiplier : InfinitySimpleRing E G :=
  algebraMap (InfinityTargetRing E G) _
    (IsLocalization.Away.invSelf (infinityScaledY E G)) *
      algebraMap (InfinityTargetRing E G) _ (infinityTargetXFactor E G)

omit [CharZero K] in
/-- Both normalizing factors are actual units on the constructed neighborhood. -/
theorem infinitySimpleMultiplier_isUnit : IsUnit (infinitySimpleMultiplier E G) := by
  apply IsUnit.mul
  · apply IsUnit.map
    apply isUnit_iff_exists_inv.mpr
    exact ⟨algebraMap (InfinityKernelRing E G) _ (infinityScaledY E G), by
      rw [mul_comm, IsLocalization.Away.mul_invSelf]⟩
  · exact IsLocalization.Away.algebraMap_isUnit (infinityTargetXFactor E G)

variable (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q)

/-- Exact parameter comparison for the original restricted target chart map. -/
theorem infinitySimpleChart_parameter :
    infinitySimpleChart E G hodd (coord (curve E G) 1 0) =
      infinitySimpleU E G * infinitySimpleMultiplier E G := by
  rw [infinitySimpleChart, AlgHom.comp_apply]
  simp only [infinityTargetChart, evaluation_coord, infinityTargetCoordinates]
  change algebraMap (InfinityTargetRing E G) _
    (IsLocalization.Away.invSelf (infinityScaledY E G) *
      algebraMap (InfinityKernelRing E G) _ (infinityScaledX E G)) = _
  rw [infinityScaledX_eq_u_mul, map_mul, map_mul, map_mul]
  change _ = infinitySimpleU E G *
    (algebraMap (InfinityTargetRing E G) _
      (IsLocalization.Away.invSelf (infinityScaledY E G)) *
        algebraMap (InfinityTargetRing E G) _ (infinityTargetXFactor E G))
  change _ = algebraMap (InfinityTargetRing E G) _
    (algebraMap (InfinityKernelRing E G) _ (infinityU E G)) * _
  unfold infinityTargetXFactor
  exact mul_left_comm _ _ _

/-- The full target identity ideal pulls back to the full source identity ideal. -/
theorem infinitySimpleChart_fiber_ideal :
    Ideal.map (infinitySimpleChart E G hodd).toRingHom
      (RingHom.ker (infinityEvaluation (curve E G)).toRingHom) =
        RingHom.ker (infinitySimpleEvaluation E G).toRingHom := by
  have hle : Ideal.map (infinitySimpleChart E G hodd).toRingHom
      (RingHom.ker (infinityEvaluation (curve E G)).toRingHom) ≤
        RingHom.ker (infinitySimpleEvaluation E G).toRingHom := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    change infinitySimpleEvaluation E G (infinitySimpleChart E G hodd x) = 0
    change ((infinitySimpleEvaluation E G).comp (infinitySimpleChart E G hodd)) x = 0
    rw [infinitySimpleChart_evaluation]
    exact hx
  refine le_antisymm hle ?_
  rw [infinitySimpleEvaluation_ker,
    ← Ideal.span_singleton_mul_right_unit (infinitySimpleMultiplier_isUnit E G),
    ← infinitySimpleChart_parameter E G hodd]
  apply Ideal.span_le.mpr
  rintro x (rfl : x = _)
  exact Ideal.mem_map_of_mem _ (by simp [RingHom.mem_ker])

end WeierstrassCurve.Velu
