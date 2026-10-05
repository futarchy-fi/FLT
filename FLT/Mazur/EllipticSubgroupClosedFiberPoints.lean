/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSubgroupIntegralSection
public import FLT.Mazur.EllipticSubgroupClosureQuasiFinite

/-!
# Closed-fiber points come from actual integral subgroup sections

Every prime in a chart's closed fiber is the reduction of an actual subgroup
point integral in that chart. This is a statement about the underlying points;
it does not assert that the special fiber is reduced.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.EllipticSubgroupChart

open WeierstrassIntegralChart

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point) (j : Fin 3)

/-- Generic evaluation is the scalar extension of the integral closure point. -/
theorem pointEvaluation_integral (P : Index A W H j)
    (hj : IsUnit ((primitiveLift A W P.1.1).coords j)) :
    pointEvaluation A W H j P =
      (Algebra.ofId A K).comp (integralClosureEvaluation A W H j P.1 hj) := by
  apply Ideal.Quotient.algHom_ext
  apply hom_ext
  intro i
  change pointEvaluation A W H j P (Ideal.Quotient.mk _ (coord W j i)) =
    (integralEvaluation A W H j P.1 hj (coord W j i) : K)
  rw [pointEvaluation_coord, integralEvaluation_coord_generic]
  rfl

/-- The generic and integral evaluations have the same kernel when the point is integral. -/
theorem pointEvaluation_kernel_integral (P : Index A W H j)
    (hj : IsUnit ((primitiveLift A W P.1.1).coords j)) :
    RingHom.ker (pointEvaluation A W H j P).toRingHom =
      RingHom.ker (integralClosureEvaluation A W H j P.1 hj).toRingHom := by
  rw [pointEvaluation_integral A W H j P hj]
  ext x
  change (integralClosureEvaluation A W H j P.1 hj x : K) = 0 ↔
    integralClosureEvaluation A W H j P.1 hj x = 0
  constructor
  · exact fun h => Subtype.coe_injective h
  · exact fun h => congrArg (fun a : A => (a : K)) h

/-- A point kernel meeting the closed fiber must have a unit chart denominator. -/
theorem isUnit_denominator_of_closed_fiber (P : Index A W H j)
    (q : closureChart A W H j)
    (hq : closureChartToBase A W H j q = IsLocalRing.closedPoint A)
    (hP : RingHom.ker (pointEvaluation A W H j P).toRingHom ≤ q.asIdeal) :
    IsUnit ((primitiveLift A W P.1.1).coords j) := by
  have hn := denominator_not_mem_of_kernel_le A W H j P q hP
  have he : q.asIdeal.comap (algebraMap A (Closure A W H j)) =
      IsLocalRing.maximalIdeal A := congrArg PrimeSpectrum.asIdeal hq
  have hm : (primitiveLift A W P.1.1).coords j ∉ IsLocalRing.maximalIdeal A := by
    rw [← he]
    exact hn
  simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] using hm

/-- Every closed-fiber chart point is the reduction of an actual integral subgroup point. -/
theorem closed_fiber_exists_integral_point [Finite H] (q : closureChart A W H j)
    (hq : closureChartToBase A W H j q = IsLocalRing.closedPoint A) :
    ∃ (P : H) (hj : IsUnit ((primitiveLift A W P.1).coords j)),
      integralChartPoint A W H j P hj (IsLocalRing.closedPoint A) = q := by
  obtain ⟨P, hP, _⟩ := exists_point_kernel_le A W H j q
  have hj := isUnit_denominator_of_closed_fiber A W H j P q hq hP
  rw [pointEvaluation_kernel_integral A W H j P hj] at hP
  have hr : q ∈ Set.range (PrimeSpectrum.comap
      (integralClosureEvaluation A W H j P.1 hj).toRingHom) := by
    rw [range_comap_of_surjective _ _ (integralClosureEvaluation_surjective A W H j P.1 hj)]
    exact hP
  obtain ⟨x, hx⟩ := hr
  have hx' : integralChartPoint A W H j P.1 hj x = q := hx
  have hb : x = IsLocalRing.closedPoint A := by
    have h := congrArg (closureChartToBase A W H j) hx'
    change (integralChartPoint A W H j P.1 hj ≫ closureChartToBase A W H j) x = _ at h
    rw [integralChartPoint_toBase, hq] at h
    exact h
  exact ⟨P.1, hj, hb ▸ hx'⟩

end FLT.Mazur.EllipticSubgroupChart
