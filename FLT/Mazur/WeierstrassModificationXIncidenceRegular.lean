/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXLocalization
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# The incidence coordinate is regular in the actual x-direction algebra

Over a domain with nonzero scale, the prime polynomial t does not divide the
incidence equation: specializing t to zero gives the nonzero constant -s.
Prime divisibility therefore proves that t remains regular in the equation
quotient. Inverting t loses no functions of the actual x-direction chart.
-/

@[expose] public noncomputable section

open Polynomial

namespace FLT.Mazur.WeierstrassModificationX

variable {R : Type*} [CommRing R]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)

/-- The incidence polynomial does not acquire a factor t when the scale is nonzero. -/
theorem incidence_not_dvd_polynomial (hs : s ≠ 0) :
    ¬ (C X : R[X][X]) ∣ polynomial W s b3 b4 b6 := by
  rintro ⟨q, hq⟩
  have h := congrArg (Polynomial.map (Polynomial.evalRingHom (0 : R))) hq
  have he : (polynomial W s b3 b4 b6).map (Polynomial.evalRingHom (0 : R)) = -C s := by
    simp [polynomial]
  rw [he, Polynomial.map_mul] at h
  have hz : (C X : R[X][X]).map (Polynomial.evalRingHom (0 : R)) = 0 := by simp
  rw [hz, zero_mul] at h
  exact hs (C_eq_zero.mp (neg_eq_zero.mp h))

variable [IsDomain R]

/-- Multiplication by the incidence coordinate kills no nonzero function. -/
theorem eq_zero_of_t_mul (hs : s ≠ 0) (z : Coordinate W s b3 b4 b6)
    (hz : t W s b3 b4 b6 * z = 0) : z = 0 := by
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective z
  change AdjoinRoot.mk _ (C X) * AdjoinRoot.mk _ g = 0 at hz
  rw [← map_mul, AdjoinRoot.mk_eq_zero] at hz
  obtain ⟨q, hq⟩ := hz
  have hp : Prime (C X : R[X][X]) := Polynomial.prime_C_iff.mpr Polynomial.prime_X
  have hd : (C X : R[X][X]) ∣ q := by
    apply (hp.dvd_mul.mp ?_).resolve_left (incidence_not_dvd_polynomial W s b3 b4 b6 hs)
    rw [← hq]
    exact dvd_mul_right _ _
  obtain ⟨q', rfl⟩ := hd
  apply AdjoinRoot.mk_eq_zero.mpr
  refine ⟨q', ?_⟩
  apply mul_left_cancel₀ hp.ne_zero
  calc
    (C X : R[X][X]) * g = polynomial W s b3 b4 b6 * (C X * q') := hq
    _ = C X * (polynomial W s b3 b4 b6 * q') := by ring

/-- The actual incidence coordinate is a non-zero-divisor in the equation quotient. -/
theorem t_regular (hs : s ≠ 0) : IsRegular (t W s b3 b4 b6) := by
  have hl : IsLeftRegular (t W s b3 b4 b6) :=
    isLeftRegular_iff_right_eq_zero_of_mul.mpr (eq_zero_of_t_mul W s b3 b4 b6 hs)
  refine ⟨hl, ?_⟩
  intro x y h
  exact hl (by simpa only [mul_comm] using h)

/-- The actual x-chart embeds into its proved overlap with the divided chart. -/
theorem xOpen_algebraMap_injective (hs : s ≠ 0) :
    Function.Injective (algebraMap (Coordinate W s b3 b4 b6) (XOpen W s b3 b4 b6)) := by
  apply (IsLocalization.injective_iff_isRegular (Submonoid.powers (t W s b3 b4 b6))).mpr
  rintro ⟨a, ha⟩
  obtain ⟨n, rfl⟩ := ha
  exact (t_regular W s b3 b4 b6 hs).pow n

end FLT.Mazur.WeierstrassModificationX
