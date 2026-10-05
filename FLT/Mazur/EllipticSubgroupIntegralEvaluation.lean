/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSubgroupChartClosure

/-!
# Integral subgroup points factor through their chart closures

A subgroup point whose primitive j-coordinate is a unit defines an integral
point of the j-chart closure. The factorization is proved from the actual
coordinate-map kernel, and its generic coordinates remain the original point.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.EllipticSubgroupChart

open WeierstrassIntegralChart

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point) (j : Fin 3)
  (P : H) (hj : IsUnit ((primitiveLift A W P.1).coords j))

/-- An integral point in a chart is also a generic point in that chart. -/
def integralIndex : Index A W H j :=
  ⟨P, by exact_mod_cast hj.ne_zero⟩

/-- Evaluation using the primitive lift normalized by its unit j-coordinate. -/
def integralEvaluation : Coordinate W j →ₐ[A] A :=
  ((primitiveLift A W P.1).normalize j hj).chartEvaluation A W j
    (PrimitiveLift.normalize_self _ j hj)

/-- Integral normalization and generic normalization agree coordinate by coordinate. -/
theorem integralEvaluation_coord_generic (i : Fin 3) :
    (integralEvaluation A W H j P hj (coord W j i) : K) =
      coordinates A W H j (integralIndex A W H j P hj) i := by
  rw [integralEvaluation, PrimitiveLift.chartEvaluation_coord]
  change (((↑hj.unit⁻¹ : A) * (primitiveLift A W P.1).coords i : A) : K) = _
  change ((↑hj.unit⁻¹ : A) : K) * ((primitiveLift A W P.1).coords i : K) =
    ((primitiveLift A W P.1).coords j : K)⁻¹ * ((primitiveLift A W P.1).coords i : K)
  congr 1
  have hn : ((primitiveLift A W P.1).coords j : K) ≠ 0 := by exact_mod_cast hj.ne_zero
  apply (mul_left_inj' hn).mp
  rw [inv_mul_cancel₀ hn]
  change (((↑hj.unit⁻¹ : A) * (primitiveLift A W P.1).coords j : A) : K) = 1
  rw [Units.inv_mul_eq_one.mpr hj.unit_spec]
  rfl

/-- Every function vanishing on the generic subgroup vanishes on its integral point. -/
theorem kernel_le_integralEvaluation :
    RingHom.ker (coordinateMap A W H j).toRingHom ≤
      RingHom.ker (integralEvaluation A W H j P hj).toRingHom := by
  have he : (Algebra.ofId A K).comp (integralEvaluation A W H j P hj) =
      (Pi.evalAlgHom A (fun _ : Index A W H j => K) (integralIndex A W H j P hj)).comp
        (coordinateMap A W H j) := by
    apply hom_ext
    intro i
    change (integralEvaluation A W H j P hj (coord W j i) : K) =
      coordinateMap A W H j (coord W j i) (integralIndex A W H j P hj)
    rw [coordinateMap_coord]
    exact integralEvaluation_coord_generic A W H j P hj i
  intro x hx
  apply Subtype.coe_injective
  change (integralEvaluation A W H j P hj x : K) = 0
  have hx' : coordinateMap A W H j x = 0 := hx
  have h := AlgHom.congr_fun he x
  change (integralEvaluation A W H j P hj x : K) =
    coordinateMap A W H j x (integralIndex A W H j P hj) at h
  rw [h, hx']
  rfl

/-- The integral point on the actual kernel-quotient closure. -/
def integralClosureEvaluation : Closure A W H j →ₐ[A] A :=
  Ideal.Quotient.liftₐ _ (integralEvaluation A W H j P hj)
    (kernel_le_integralEvaluation A W H j P hj)

/-- The closure point recovers the original integral chart evaluation. -/
theorem integralClosureEvaluation_mk (x : Coordinate W j) :
    integralClosureEvaluation A W H j P hj (Ideal.Quotient.mk _ x) =
      integralEvaluation A W H j P hj x := rfl

/-- The closure point is a retraction of the coefficient inclusion. -/
theorem integralClosureEvaluation_algebraMap (a : A) :
    integralClosureEvaluation A W H j P hj (algebraMap A (Closure A W H j) a) = a :=
  (integralClosureEvaluation A W H j P hj).commutes a

/-- The integral point is a closed immersion into its affine closure chart. -/
theorem integralClosureEvaluation_surjective :
    Function.Surjective (integralClosureEvaluation A W H j P hj) := by
  intro a
  exact ⟨algebraMap A (Closure A W H j) a,
    integralClosureEvaluation_algebraMap A W H j P hj a⟩

end FLT.Mazur.EllipticSubgroupChart
