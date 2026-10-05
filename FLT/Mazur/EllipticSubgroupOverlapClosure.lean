/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSubgroupOverlapEvaluation

/-!
# Compatibility of subgroup closure ideals on overlaps

The ambient coordinate transition carries the localized equations of the
actual subgroup to one another. Descending this transition gives inverse
algebra maps between the overlap quotients, without assuming finiteness.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.EllipticSubgroupChart

open WeierstrassIntegralChart

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point) (j k : Fin 3)

/-- The chart closure equations extended to a principal overlap. -/
def overlapIdeal : Ideal (Overlap W j k) :=
  (RingHom.ker (coordinateMap A W H j).toRingHom).map
    (algebraMap (Coordinate W j) (Overlap W j k))

/-- The localized ideal is detected precisely by the subgroup points in both charts. -/
theorem overlapIdeal_eq_kernel :
    overlapIdeal A W H j k = RingHom.ker (overlapEvaluation A W H j k).toRingHom :=
  (LocalizedPointAlgebra.kernel_evaluation (coordinateMap A W H j) (coord W j k)).symm

/-- The ambient coordinate transition preserves exactly the subgroup equations. -/
theorem transition_mem_overlapIdeal (z : Overlap W k j) :
    transition W j k z ∈ overlapIdeal A W H j k ↔ z ∈ overlapIdeal A W H k j := by
  rw [overlapIdeal_eq_kernel, overlapIdeal_eq_kernel]
  change overlapEvaluation A W H j k (transition W j k z) = 0 ↔
    overlapEvaluation A W H k j z = 0
  constructor
  · intro h
    ext P
    have hP := congrFun h (overlapIndexSwap A W H k j P)
    simpa only [overlapEvaluation_transition, overlapIndexSwap_swap, Pi.zero_apply] using hP
  · intro h
    ext P
    rw [overlapEvaluation_transition]
    exact congrFun h (overlapIndexSwap A W H j k P)

/-- The ambient overlap isomorphism identifies the two extended closure ideals. -/
theorem overlapIdeal_map :
    overlapIdeal A W H j k = (overlapIdeal A W H k j).map
      (overlapEquiv W j k).toRingEquiv.toRingHom := by
  apply le_antisymm
  · intro z hz
    have h : transition W k j z ∈ overlapIdeal A W H k j :=
      (transition_mem_overlapIdeal A W H k j z).mpr hz
    have hm := Ideal.mem_map_of_mem (overlapEquiv W j k).toRingEquiv.toRingHom h
    have he : transition W j k (transition W k j z) = z :=
      AlgHom.congr_fun (transition_comp W j k) z
    exact he ▸ hm
  · apply Ideal.map_le_iff_le_comap.mpr
    intro z hz
    exact (transition_mem_overlapIdeal A W H j k z).mpr hz

/-- The actual overlap coordinate algebra of the subgroup closure. -/
abbrev OverlapClosure := Overlap W j k ⧸ overlapIdeal A W H j k

/-- The two closure presentations give canonically equivalent overlap algebras. -/
def closureOverlapEquiv : OverlapClosure A W H k j ≃ₐ[A] OverlapClosure A W H j k :=
  Ideal.quotientEquivAlg _ _ (overlapEquiv W j k) (overlapIdeal_map A W H j k)

/-- The descended map is the original coordinate transition modulo the equations. -/
@[simp] theorem closureOverlapEquiv_mk (z : Overlap W k j) :
    closureOverlapEquiv A W H j k (Ideal.Quotient.mk _ z) =
      Ideal.Quotient.mk _ (transition W j k z) := rfl

/-- The descended overlap transitions are inverse. -/
theorem closureOverlapEquiv_comp (z : OverlapClosure A W H j k) :
    closureOverlapEquiv A W H j k (closureOverlapEquiv A W H k j z) = z := by
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [closureOverlapEquiv_mk, closureOverlapEquiv_mk]
  exact congrArg (Ideal.Quotient.mk _) (AlgHom.congr_fun (transition_comp W j k) z)

end FLT.Mazur.EllipticSubgroupChart
