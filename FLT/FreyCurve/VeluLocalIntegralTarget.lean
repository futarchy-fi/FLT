/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Basic
public import FLT.FreyCurve.Serre.VeluLocalIntegralModel

/-!
# Integral local Vélu targets of the normalized Frey curve

The source model is the actual integral Frey equation. For a finite local
p-kernel, the target model follows from the torsion ramification theorem;
neither coordinate integrality nor target semistability is an input.
-/

@[expose] public section

namespace FreyPackage

open IsLocalRing WeierstrassCurve

variable (P : FreyPackage) {K : Type*} [Field K] [Algebra ℚ K]
variable (A : ValuationSubring K)

/-- The normalized integer Frey equation supplies the local integral source model. -/
theorem integral_local_source :
    (P.freyCurveInt.map (algebraMap ℤ A)).map (algebraMap A K) =
      P.freyCurve.map (algebraMap ℚ K) := by
  rw [← FreyCurve.map P, WeierstrassCurve.map_map, WeierstrassCurve.map_map]
  congr 1
  exact Subsingleton.elim _ _

variable [DecidableEq K] [IsAdicComplete (maximalIdeal A) A]
variable [IsDiscreteValuationRing A]
variable (G : AddSubgroup (P.freyCurve.map (algebraMap ℚ K)).toAffine.Point) [Fintype G]
variable (hG : ∀ Q : G, P.p • Q.val = 0)

include hG

/-- Actual local prime kernels on the Frey equation have integral Vélu targets. -/
theorem exists_integral_local_velu_target (hp0 : (P.p : A) ≠ 0)
    (he : RaynaudParameters.order (P.p : A) < P.p - 1) :
    ∃ U : WeierstrassCurve A, U.map (algebraMap A K) =
      Velu.curve (P.freyCurve.map (algebraMap ℚ K)) G := by
  let _ : Fact P.p.Prime := ⟨P.pp⟩
  let _ : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  exact Velu.exists_prime_kernel_integral_model A
    (P.freyCurveInt.map (algebraMap ℤ A)) P.p (by linarith [P.hp5])
    _ (P.integral_local_source A) G hG hp0 he

/-- Away from p no ramification bound is needed for a local Frey Vélu target. -/
theorem exists_integral_local_velu_target_of_unit (hp : IsUnit (P.p : A)) :
    ∃ U : WeierstrassCurve A, U.map (algebraMap A K) =
      Velu.curve (P.freyCurve.map (algebraMap ℚ K)) G := by
  let _ : Fact P.p.Prime := ⟨P.pp⟩
  let _ : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  exact Velu.exists_prime_kernel_integral_model_of_unit A
    (P.freyCurveInt.map (algebraMap ℤ A)) P.p (by linarith [P.hp5])
    _ (P.integral_local_source A) G hG hp

end FreyPackage
