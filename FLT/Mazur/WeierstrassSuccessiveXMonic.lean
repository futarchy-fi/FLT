/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.SuccessiveIncidenceAlgebra

/-!
# The monic slope algebra over the incidence base

Adjoin the slope v by its monic quadratic over R[t,u]/(t*u-π).
The resulting algebra is free over the incidence base, so regularity of t
survives. The comparison with the actual three-generator presentation is separate.
-/

@[expose] public noncomputable section

open Polynomial

namespace FLT.Mazur.WeierstrassSuccessiveX

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)

/-- The monic slope equation over the incidence algebra. -/
def slopePolynomial : (SuccessiveIncidence.Coordinate π)[X] :=
  X ^ 2 + C (algebraMap R _ W.a₁ + algebraMap R _ b3 * SuccessiveIncidence.t π) * X -
    C (algebraMap R _ s * SuccessiveIncidence.u π + algebraMap R _ W.a₂ +
      algebraMap R _ b4 * SuccessiveIncidence.t π +
      algebraMap R _ b6 * SuccessiveIncidence.t π ^ 2)

/-- The slope equation is monic independently of the preceding scale. -/
theorem slopePolynomial_monic : (slopePolynomial W s π b3 b4 b6).Monic := by
  have he : slopePolynomial W s π b3 b4 b6 = Cubic.toPoly
      ⟨0, 1, algebraMap R _ W.a₁ + algebraMap R _ b3 * SuccessiveIncidence.t π,
        -(algebraMap R _ s * SuccessiveIncidence.u π + algebraMap R _ W.a₂ +
          algebraMap R _ b4 * SuccessiveIncidence.t π +
          algebraMap R _ b6 * SuccessiveIncidence.t π ^ 2)⟩ := by
    simp only [slopePolynomial, Cubic.toPoly, C_0, C_1, C_neg, zero_mul, one_mul, zero_add]
    ring
  rw [he]
  exact Cubic.monic_of_b_eq_one'

/-- The iterated quotient, monic in the slope coordinate. -/
abbrev MonicCoordinate := AdjoinRoot (slopePolynomial W s π b3 b4 b6)

/-- The incidence ratio in the monic presentation. -/
def monicT : MonicCoordinate W s π b3 b4 b6 :=
  algebraMap (SuccessiveIncidence.Coordinate π) _ (SuccessiveIncidence.t π)

/-- The slope in the monic presentation. -/
def monicV : MonicCoordinate W s π b3 b4 b6 :=
  AdjoinRoot.root (slopePolynomial W s π b3 b4 b6)

/-- The retained horizontal coordinate in the monic presentation. -/
def monicU : MonicCoordinate W s π b3 b4 b6 :=
  algebraMap (SuccessiveIncidence.Coordinate π) _ (SuccessiveIncidence.u π)

/-- Evaluation expands the monic slope relation. -/
theorem slopePolynomial_eval {S : Type*} [CommRing S]
    (f : SuccessiveIncidence.Coordinate π →+* S) (v : S) :
    (slopePolynomial W s π b3 b4 b6).eval₂ f v =
      v ^ 2 + (f (algebraMap R _ W.a₁) + f (algebraMap R _ b3) *
        f (SuccessiveIncidence.t π)) * v -
      (f (algebraMap R _ s) * f (SuccessiveIncidence.u π) + f (algebraMap R _ W.a₂) +
        f (algebraMap R _ b4) * f (SuccessiveIncidence.t π) +
        f (algebraMap R _ b6) * f (SuccessiveIncidence.t π) ^ 2) := by
  simp only [slopePolynomial, eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X,
    eval₂_C, map_add, map_mul, map_pow]

/-- The monic presentation satisfies its actual slope equation. -/
theorem monic_equation :
    monicV W s π b3 b4 b6 ^ 2 +
      (algebraMap R _ W.a₁ + algebraMap R _ b3 * monicT W s π b3 b4 b6) *
        monicV W s π b3 b4 b6 =
      algebraMap R _ s * monicU W s π b3 b4 b6 + algebraMap R _ W.a₂ +
        algebraMap R _ b4 * monicT W s π b3 b4 b6 +
        algebraMap R _ b6 * monicT W s π b3 b4 b6 ^ 2 := by
  have h := AdjoinRoot.eval₂_root (slopePolynomial W s π b3 b4 b6)
  rw [slopePolynomial_eval] at h
  have hc (a : R) : algebraMap (SuccessiveIncidence.Coordinate π)
      (MonicCoordinate W s π b3 b4 b6) (algebraMap R _ a) = algebraMap R _ a :=
    (IsScalarTower.algebraMap_apply R (SuccessiveIncidence.Coordinate π) _ a).symm
  simpa only [AdjoinRoot.algebraMap_eq, ← hc, sub_eq_zero, monicT, monicV, monicU] using h

/-- The monic presentation retains the incidence relation. -/
theorem monic_incidence : monicT W s π b3 b4 b6 * monicU W s π b3 b4 b6 =
    algebraMap R _ π := by
  rw [monicT, monicU, ← map_mul, SuccessiveIncidence.incidence,
    ← IsScalarTower.algebraMap_apply]

/-- The monic presentation is free over the actual incidence algebra. -/
instance monicCoordinate_free :
    Module.Free (SuccessiveIncidence.Coordinate π) (MonicCoordinate W s π b3 b4 b6) :=
  (slopePolynomial_monic W s π b3 b4 b6).free_adjoinRoot

/-- The incidence ratio remains regular after adjoining the monic slope. -/
theorem monicT_regular [IsDomain R] (hπ : π ≠ 0) :
    IsRegular (monicT W s π b3 b4 b6) :=
  WeierstrassIntegralChart.flatRingHom_isRegular _
    (RingHom.flat_algebraMap_iff.mpr inferInstance) (SuccessiveIncidence.t_regular π hπ)

end FLT.Mazur.WeierstrassSuccessiveX
