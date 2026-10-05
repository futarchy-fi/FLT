/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSubgroupChartGeneric
public import FLT.Mazur.EllipticSubgroupIntegralEvaluation
public import FLT.Mazur.FinitePointKernelCover

/-!
# Point kernels and specialization in subgroup closure charts

Each prime of a finite subgroup closure contains one point kernel. The primitive
coordinate relations force the chart denominator to avoid that prime. Thus a
point cannot acquire a specialization in a chart which its section has left.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.EllipticSubgroupChart

open WeierstrassIntegralChart

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point) (j : Fin 3)

/-- Generic evaluation of the closure at one actual subgroup point. -/
abbrev pointEvaluation (P : Index A W H j) : Closure A W H j →ₐ[A] K :=
  FinitePointKernelCover.evaluation (coordinateMap A W H j) P

/-- The coordinates of a closure point are the normalized generic coordinates. -/
theorem pointEvaluation_coord (P : Index A W H j) (i : Fin 3) :
    pointEvaluation A W H j P (Ideal.Quotient.mk _ (coord W j i)) =
      coordinates A W H j P i := by
  rw [pointEvaluation, FinitePointKernelCover.evaluation_mk, coordinateMap_coord]

/-- The primitive linear relations vanish at the corresponding generic point. -/
theorem primitive_relation_mem_kernel (P : Index A W H j) (i : Fin 3) :
    algebraMap A (Closure A W H j) ((primitiveLift A W P.1.1).coords j) *
        Ideal.Quotient.mk _ (coord W j i) -
      algebraMap A (Closure A W H j) ((primitiveLift A W P.1.1).coords i) ∈
        RingHom.ker (pointEvaluation A W H j P).toRingHom := by
  change pointEvaluation A W H j P _ = 0
  rw [map_sub, map_mul, AlgHom.commutes, AlgHom.commutes, pointEvaluation_coord]
  change ((primitiveLift A W P.1.1).coords j : K) *
      (((primitiveLift A W P.1.1).coords j : K)⁻¹ *
        (primitiveLift A W P.1.1).coords i) - (primitiveLift A W P.1.1).coords i = 0
  rw [← mul_assoc, mul_inv_cancel₀ P.2, one_mul, sub_self]

/-- No prime containing a point kernel can contain that point's chart denominator. -/
theorem denominator_not_mem_of_kernel_le (P : Index A W H j)
    (q : PrimeSpectrum (Closure A W H j))
    (hP : RingHom.ker (pointEvaluation A W H j P).toRingHom ≤ q.asIdeal) :
    algebraMap A (Closure A W H j) ((primitiveLift A W P.1.1).coords j) ∉ q.asIdeal := by
  intro hd
  obtain ⟨i, hi⟩ := (primitiveLift A W P.1.1).primitive
  have hm := q.asIdeal.mul_mem_right (Ideal.Quotient.mk _ (coord W j i)) hd
  have hr := hP (primitive_relation_mem_kernel A W H j P i)
  have hc : algebraMap A (Closure A W H j) ((primitiveLift A W P.1.1).coords i) ∈
      q.asIdeal := by
    simpa only [sub_sub_cancel] using q.asIdeal.sub_mem hm hr
  exact q.isPrime.ne_top (q.asIdeal.eq_top_of_isUnit_mem hc (hi.map _))

/-- Every prime belongs to some actual point closure, on its allowed base open. -/
theorem exists_point_kernel_le [Finite H] (q : PrimeSpectrum (Closure A W H j)) :
    ∃ P : Index A W H j,
      RingHom.ker (pointEvaluation A W H j P).toRingHom ≤ q.asIdeal ∧
        algebraMap A (Closure A W H j) ((primitiveLift A W P.1.1).coords j) ∉ q.asIdeal := by
  obtain ⟨P, hP⟩ := FinitePointKernelCover.exists_kernel_le (coordinateMap A W H j) q
  exact ⟨P, hP, denominator_not_mem_of_kernel_le A W H j P q hP⟩

end FLT.Mazur.EllipticSubgroupChart
