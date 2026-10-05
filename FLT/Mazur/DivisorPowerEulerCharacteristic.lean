/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorTwistedDegree
public import FLT.Mazur.AmpleAffinePullback
public import FLT.Mazur.DivisorLineBundlePower

/-!
# Euler characteristic and section growth for powers of a finite divisor

The twisted exact sequence gives the linear power formula for O(D). This is
an effective-divisor result; realization of an arbitrary line sheaf by rational
divisors, and the positive-degree ampleness implication, are separate steps.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve

open ModuleLineBundleTensorPullback

variable {k : Type} [Field k] {X : Scheme}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
  {I : X.IdealSheafData} (hI : EffectiveCartier I) [IsFinite (I.subschemeι ≫ f)]

/-- Euler characteristic of an effective-divisor line grows linearly with its tensor power. -/
theorem curveEulerCharacteristic_divisor_power (n : ℕ) :
    curveEulerCharacteristic f (tensorPower (divisorLineBundle I hI) n) =
      (n : ℤ) * (divisorFieldLength f I : ℤ) +
        curveEulerCharacteristic f (structureModule X) := by
  induction n with
  | zero => simp only [tensorPower, Nat.cast_zero, zero_mul, zero_add]
  | succ n ih =>
    change curveEulerCharacteristic f
      (ModuleSheafTensor.tensor (divisorLineBundle I hI)
        (tensorPower (divisorLineBundle I hI) n)) = _
    rw [curveEulerCharacteristic_divisor_tensor f hI
      (hI.divisorLineBundle_locallyFreeRankOne.tensorPower n), ih, Nat.cast_add, Nat.cast_one]
    ring

/-- The degree of a tensor power of O(D) is the exponent times the divisor length. -/
theorem curveSheafDegree_divisor_power (n : ℕ) :
    curveSheafDegree f (tensorPower (divisorLineBundle I hI) n) =
      (n : ℤ) * (divisorFieldLength f I : ℤ) := by
  unfold curveSheafDegree
  rw [curveEulerCharacteristic_divisor_power f hI n]
  exact add_sub_cancel_right _ _

/-- The power formula also holds for the actual sheaf O(nD). -/
theorem curveSheafDegree_divisor_ideal_power (n : ℕ) :
    curveSheafDegree f (divisorLineBundle (I ^ n) (hI.pow n)) =
      (n : ℤ) * curveSheafDegree f (divisorLineBundle I hI) := by
  rw [← curveSheafDegree_iso f (divisorLineBundlePowerIso hI n),
    curveSheafDegree_divisor_power f hI n, divisor_degree_eq_fieldLength f hI]

/-- Nonnegative H¹ gives the expected lower bound on sections of O(nD). -/
theorem divisor_power_h0_lower_bound (n : ℕ) :
    (n : ℤ) * (divisorFieldLength f I : ℤ) +
      curveEulerCharacteristic f (structureModule X) ≤
        (Module.finrank k (ModuleScalarH f
          (tensorPower (divisorLineBundle I hI) n) 0) : ℤ) := by
  have h := curveEulerCharacteristic_divisor_power f hI n
  unfold curveEulerCharacteristic at h ⊢
  omega

/-- Positive finite divisor length forces arbitrarily many sections in positive powers. -/
theorem divisor_power_h0_unbounded (hd : 0 < divisorFieldLength f I) (b : ℕ) :
    ∃ n : ℕ, 0 < n ∧ b < Module.finrank k
      (ModuleScalarH f (tensorPower (divisorLineBundle I hI) n) 0) := by
  obtain ⟨m, hm⟩ := exists_nat_gt
    ((b : ℤ) - curveEulerCharacteristic f (structureModule X))
  refine ⟨m + 1, by omega, ?_⟩
  have hg := divisor_power_h0_lower_bound f hI (m + 1)
  have hp : (1 : ℤ) ≤ (divisorFieldLength f I : ℤ) := by exact_mod_cast hd
  have hm0 : (0 : ℤ) ≤ m := Nat.cast_nonneg m
  push_cast at hg
  have : (b : ℤ) < (Module.finrank k
      (ModuleScalarH f (tensorPower (divisorLineBundle I hI) (m + 1)) 0) : ℤ) := by
    nlinarith
  exact_mod_cast this

end FLT.Mazur.FCurve
