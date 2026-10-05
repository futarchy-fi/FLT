/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSubgroupChartClosure
public import FLT.Mazur.LocalizedPointAlgebraKernel
public import FLT.Mazur.WeierstrassChartOverlap

/-!
# Subgroup evaluation on chart overlaps

The points retained by localizing a chart are exactly the subgroup points
lying in both charts. Swapping the charts preserves this index set, and the
explicit ambient transition agrees with evaluating the renormalized points.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.EllipticSubgroupChart

open WeierstrassIntegralChart

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point) (j k : Fin 3)

/-- A normalized coordinate is nonzero exactly when the primitive coordinate is. -/
theorem coordinates_ne_zero_iff (P : Index A W H j) (i : Fin 3) :
    coordinates A W H j P i ≠ 0 ↔ ((primitiveLift A W P.1.1).coords i : K) ≠ 0 := by
  change ((primitiveLift A W P.1.1).coords j : K)⁻¹ *
    (primitiveLift A W P.1.1).coords i ≠ 0 ↔ _
  exact mul_ne_zero_iff.trans (and_iff_right (inv_ne_zero P.2))

/-- Subgroup points retained on the overlap of two charts. -/
abbrev OverlapIndex :=
  LocalizedPointAlgebra.Index (coordinateMap A W H j) (coord W j k)

/-- The same subgroup point viewed from the second chart. -/
def overlapIndexSwap (P : OverlapIndex A W H j k) : OverlapIndex A W H k j := by
  have hk : coordinates A W H j P.1 k ≠ 0 := by
    simpa only [coordinateMap_coord] using P.2
  let Q : Index A W H k :=
    ⟨P.1.1, (coordinates_ne_zero_iff A W H j P.1 k).mp hk⟩
  refine ⟨Q, ?_⟩
  rw [coordinateMap_coord, coordinates_ne_zero_iff]
  exact P.1.2

/-- Swapping the chart order twice leaves the point unchanged. -/
@[simp] theorem overlapIndexSwap_swap (P : OverlapIndex A W H j k) :
    overlapIndexSwap A W H k j (overlapIndexSwap A W H j k P) = P := rfl

/-- The two orders of the overlap have canonically the same subgroup points. -/
def overlapIndexEquiv : OverlapIndex A W H j k ≃ OverlapIndex A W H k j where
  toFun := overlapIndexSwap A W H j k
  invFun := overlapIndexSwap A W H k j
  left_inv := overlapIndexSwap_swap A W H j k
  right_inv := overlapIndexSwap_swap A W H k j

/-- Switching charts divides each coordinate by the second chart coordinate. -/
theorem coordinates_swap (P : OverlapIndex A W H j k) (i : Fin 3) :
    coordinates A W H k (overlapIndexSwap A W H j k P).1 i =
      (coordinates A W H j P.1 k)⁻¹ * coordinates A W H j P.1 i := by
  change ((primitiveLift A W P.1.1.1).coords k : K)⁻¹ *
      (primitiveLift A W P.1.1.1).coords i =
    (((primitiveLift A W P.1.1.1).coords j : K)⁻¹ *
      (primitiveLift A W P.1.1.1).coords k)⁻¹ *
    (((primitiveLift A W P.1.1.1).coords j : K)⁻¹ *
      (primitiveLift A W P.1.1.1).coords i)
  rw [mul_inv_rev, inv_inv]
  rw [mul_assoc, ← mul_assoc ((primitiveLift A W P.1.1.1).coords j : K),
    mul_inv_cancel₀ P.1.2, one_mul]

/-- The actual subgroup evaluations on the localized ambient chart. -/
def overlapEvaluation : Overlap W j k →ₐ[A] (OverlapIndex A W H j k → K) :=
  LocalizedPointAlgebra.evaluation (coordinateMap A W H j) (coord W j k)

/-- Overlap evaluation retains the first chart's normalized coordinates. -/
@[simp] theorem overlapEvaluation_coord (P : OverlapIndex A W H j k) (i : Fin 3) :
    overlapEvaluation A W H j k (overlapCoord W j k i) P = coordinates A W H j P.1 i :=
by
  rw [overlapEvaluation, overlapCoord, LocalizedPointAlgebra.evaluation_algebraMap,
    coordinateMap_coord]

/-- The inverse normalizing coordinate evaluates to its field inverse. -/
@[simp] theorem overlapEvaluation_inverse (P : OverlapIndex A W H j k) :
    overlapEvaluation A W H j k (overlapInverse W j k) P =
      (coordinates A W H j P.1 k)⁻¹ := by
  have hk : coordinates A W H j P.1 k ≠ 0 := by
    simpa only [coordinateMap_coord] using P.2
  apply (mul_left_inj' hk).mp
  have h := congrArg (fun z => overlapEvaluation A W H j k z P)
    (overlapInverse_mul W j k)
  rw [map_mul, Pi.mul_apply, overlapEvaluation_coord, map_one, Pi.one_apply] at h
  exact h.trans (inv_mul_cancel₀ hk).symm

/-- The ambient transition evaluates to the same actual subgroup point. -/
theorem overlapEvaluation_transition (z : Overlap W k j) (P : OverlapIndex A W H j k) :
    overlapEvaluation A W H j k (transition W j k z) P =
      overlapEvaluation A W H k j z (overlapIndexSwap A W H j k P) := by
  let ev := Pi.evalAlgHom A (fun _ : OverlapIndex A W H j k => K) P
  let ev' := Pi.evalAlgHom A (fun _ : OverlapIndex A W H k j => K)
    (overlapIndexSwap A W H j k P)
  have h : (ev.comp (overlapEvaluation A W H j k)).comp (transition W j k) =
      ev'.comp (overlapEvaluation A W H k j) := by
    apply IsLocalization.algHom_ext (Submonoid.powers (coord W k j))
    apply hom_ext
    intro i
    change overlapEvaluation A W H j k (transition W j k (overlapCoord W k j i)) P = _
    rw [transition_coord, map_mul, Pi.mul_apply, overlapEvaluation_inverse,
      overlapEvaluation_coord]
    change _ = overlapEvaluation A W H k j (overlapCoord W k j i)
      (overlapIndexSwap A W H j k P)
    rw [overlapEvaluation_coord]
    exact (coordinates_swap A W H j k P i).symm
  exact AlgHom.congr_fun h z

end FLT.Mazur.EllipticSubgroupChart
