/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationAlgebra
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# The incidence base of a successive modification

The algebra R[t,u]/(t*u-π) retains both coordinates. When R is a domain
and π is nonzero, t is regular. This supplies the base for the monic slope
presentation of the successive three-generator chart.
-/

@[expose] public noncomputable section

open Polynomial

namespace FLT.Mazur.SuccessiveIncidence

variable {R : Type*} [CommRing R] (π : R)

/-- The incidence equation, with t in the coefficient ring and u the root. -/
def polynomial : R[X][X] := C X * X - C (C π)

/-- The actual two-coordinate incidence algebra. -/
abbrev Coordinate := AdjoinRoot (polynomial π)

/-- The incidence ratio. -/
def t : Coordinate π := algebraMap R[X] _ X

/-- The retained horizontal coordinate. -/
def u : Coordinate π := AdjoinRoot.root (polynomial π)

/-- Evaluation of the incidence equation. -/
theorem polynomial_eval {S : Type*} [CommRing S] (f : R[X] →+* S) (z : S) :
    (polynomial π).eval₂ f z = f X * z - f (C π) := by
  simp only [polynomial, eval₂_sub, eval₂_mul, eval₂_C, eval₂_X]

/-- The two coordinates recover the base parameter. -/
theorem incidence : t π * u π = algebraMap R _ π := by
  have h := AdjoinRoot.eval₂_root (polynomial π)
  rw [polynomial_eval] at h
  have hc : algebraMap R[X] (Coordinate π) (C π) = algebraMap R _ π :=
    (IsScalarTower.algebraMap_apply R R[X] _ π).symm
  simpa only [AdjoinRoot.algebraMap_eq, ← hc, sub_eq_zero, t, u] using h

/-- Solutions of the incidence equation induce algebra maps. -/
def evaluation {S : Type*} [CommRing S] [Algebra R S] (a b : S)
    (h : a * b = algebraMap R S π) : Coordinate π →ₐ[R] S :=
  AdjoinRoot.liftAlgHom (polynomial π) (aeval a) b (by
    rw [polynomial_eval]
    simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_X, aeval_C,
      sub_eq_zero] using h)

/-- Evaluation preserves the incidence ratio. -/
@[simp] theorem evaluation_t {S : Type*} [CommRing S] [Algebra R S] (a b : S) (h) :
    evaluation π a b h (t π) = a := by
  simp [evaluation, t, AdjoinRoot.algebraMap_eq, AdjoinRoot.liftAlgHom_of]

/-- Evaluation preserves the retained horizontal coordinate. -/
@[simp] theorem evaluation_u {S : Type*} [CommRing S] [Algebra R S] (a b : S) (h) :
    evaluation π a b h (u π) = b := AdjoinRoot.liftAlgHom_root _ _ _ _

/-- Both incidence coordinates determine a map. -/
@[ext] theorem hom_ext {S : Type*} [CommRing S] [Algebra R S]
    (f g : Coordinate π →ₐ[R] S) (ht : f (t π) = g (t π))
    (hu : f (u π) = g (u π)) : f = g := by
  apply AdjoinRoot.algHom_ext'
  · exact Polynomial.algHom_ext ht
  · exact hu

/-- The incidence equation is not divisible by t if the parameter is nonzero. -/
theorem t_not_dvd_polynomial (hπ : π ≠ 0) : ¬ (C X : R[X][X]) ∣ polynomial π := by
  rintro ⟨q, hq⟩
  have h := congrArg (Polynomial.map (Polynomial.evalRingHom (0 : R))) hq
  have he : (polynomial π).map (Polynomial.evalRingHom (0 : R)) = -C π := by
    simp [polynomial]
  rw [he, Polynomial.map_mul] at h
  have hz : (C X : R[X][X]).map (Polynomial.evalRingHom (0 : R)) = 0 := by simp
  rw [hz, zero_mul] at h
  exact hπ (C_eq_zero.mp (neg_eq_zero.mp h))

variable [IsDomain R]

/-- Multiplication by t cannot kill a nonzero incidence function. -/
theorem eq_zero_of_t_mul (hπ : π ≠ 0) (z : Coordinate π) (hz : t π * z = 0) : z = 0 := by
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective z
  change AdjoinRoot.mk _ (C X) * AdjoinRoot.mk _ g = 0 at hz
  rw [← map_mul, AdjoinRoot.mk_eq_zero] at hz
  obtain ⟨q, hq⟩ := hz
  have hp : Prime (C X : R[X][X]) := Polynomial.prime_C_iff.mpr Polynomial.prime_X
  have hd : (C X : R[X][X]) ∣ q := by
    apply (hp.dvd_mul.mp ?_).resolve_left (t_not_dvd_polynomial π hπ)
    rw [← hq]
    exact dvd_mul_right _ _
  obtain ⟨q', rfl⟩ := hd
  apply AdjoinRoot.mk_eq_zero.mpr
  refine ⟨q', ?_⟩
  apply mul_left_cancel₀ hp.ne_zero
  calc
    (C X : R[X][X]) * g = polynomial π * (C X * q') := hq
    _ = C X * (polynomial π * q') := by ring

/-- The incidence ratio is regular in the actual incidence algebra. -/
theorem t_regular (hπ : π ≠ 0) : IsRegular (t π) := by
  have hl : IsLeftRegular (t π) :=
    isLeftRegular_iff_right_eq_zero_of_mul.mpr (eq_zero_of_t_mul π hπ)
  exact ⟨hl, fun x y h => hl (by simpa only [mul_comm] using h)⟩

end FLT.Mazur.SuccessiveIncidence
