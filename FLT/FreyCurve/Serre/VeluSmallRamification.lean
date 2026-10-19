/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluIntegralSums
public import FLT.Mazur.EllipticSmallRamificationSpecialization

/-!
# Integral Vélu targets from actual local torsion

The formal-group ramification bound proves the coordinate hypotheses of the
coefficient-sum lemmas. No integrality of kernel coordinates is assumed here.
-/

@[expose] public section

namespace WeierstrassCurve.Velu

open IsLocalRing FLT.Mazur

variable {K : Type*} [Field K] [DecidableEq K] [NeZero (2 : K)]
variable (A : ValuationSubring K) (W : WeierstrassCurve A)
variable [IsAdicComplete (maximalIdeal A) A] [IsDiscreteValuationRing A]
variable (p : ℕ) [Fact p.Prime] (hp0 : (p : A) ≠ 0)
variable (he : RaynaudParameters.order (p : A) < p - 1)
variable (G : AddSubgroup (W.map (algebraMap A K)).toAffine.Point)
variable (hG : ∀ Q : G, p • Q.val = 0)

include hp0 he hG

omit [NeZero (2 : K)] in
/-- Every abscissa of the actual local p-kernel is integral under small ramification. -/
theorem prime_kernel_xCoord_mem (Q : G) : xCoord Q.val ∈ A := by
  have hQ := hG Q
  cases hval : Q.val with
  | zero => exact A.zero_mem
  | some x y h =>
    rw [hval] at hQ
    exact (affine_prime_torsion_coordinates_integral A W p hp0 he h hQ).1

variable [Fintype G]

/-- The local Vélu equation has integral coefficients, with coordinates proved integral. -/
theorem prime_kernel_curve_coefficients_mem (hp2 : p ≠ 2) :
    (curve (W.map (algebraMap A K)) G).a₁ ∈ A ∧
    (curve (W.map (algebraMap A K)) G).a₂ ∈ A ∧
    (curve (W.map (algebraMap A K)) G).a₃ ∈ A ∧
    (curve (W.map (algebraMap A K)) G).a₄ ∈ A ∧
    (curve (W.map (algebraMap A K)) G).a₆ ∈ A := by
  have hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q := by
    intro Q hQ
    apply ne_neg_of_odd_nsmul (Nat.Prime.odd_of_ne_two Fact.out hp2) hQ
    exact Subtype.ext (hG Q)
  exact curve_coefficients_mem_subring (W.map (algebraMap A K)) G hodd A.toSubring
    W.a₁.property W.a₂.property W.a₃.property W.a₄.property W.a₆.property
    (fun Q _ ↦ prime_kernel_xCoord_mem A W p hp0 he G hG Q)

end WeierstrassCurve.Velu
