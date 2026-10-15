/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentPairEvaluation

/-!
# Laurent evaluation modulo an annihilator

Equality after multiplication by a fixed scalar propagates through Laurent
substitution, including negative powers. This keeps square-zero corrections
under control without discarding the nonreduced coefficient algebra.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.LaurentWeightedEvaluation
open LaurentPolynomial LaurentUnitPoints LaurentPairEvaluation
variable {R B : Type*} [CommRing R] [CommRing B]

/-- Weighted equality respects multiplication of both arguments. -/
theorem weighted_mul (e a a' b b' : B) (ha : e * a = e * a')
    (hb : e * b = e * b') : e * (a * b) = e * (a' * b') := by
  calc
    e * (a * b) = (e * a) * b := (mul_assoc _ _ _).symm
    _ = (e * a') * b := by rw [ha]
    _ = a' * (e * b) := by ring
    _ = a' * (e * b') := by rw [hb]
    _ = e * (a' * b') := by ring

/-- Inverting units preserves equality modulo the annihilator of the weight. -/
theorem weighted_inv (e : B) (u v : Bˣ) (hu : e * u.val = e * v.val) :
    e * u⁻¹.val = e * v⁻¹.val := by
  have hh := congrArg (fun a : B ↦ (u⁻¹.val * v⁻¹.val) * a) hu
  have hl : (u⁻¹.val * v⁻¹.val) * (e * u.val) = e * v⁻¹.val := by
    calc
      _ = e * v⁻¹.val * (u⁻¹.val * u.val) := by ring
      _ = _ := by rw [Units.inv_mul, mul_one]
  have hr : (u⁻¹.val * v⁻¹.val) * (e * v.val) = e * u⁻¹.val := by
    calc
      _ = e * u⁻¹.val * (v⁻¹.val * v.val) := by ring
      _ = _ := by rw [Units.inv_mul, mul_one]
  exact (hl.symm.trans (hh.trans hr)).symm

/-- Weighted equality of Laurent generators and coefficients determines every evaluation. -/
theorem weighted_hom (e : B) (f g : R[T;T⁻¹] →+* B)
    (hc : ∀ r, e * f (C r) = e * g (C r))
    (hp : e * f (T 1) = e * g (T 1))
    (hn : e * f (T (-1)) = e * g (T (-1))) (p : R[T;T⁻¹]) :
    e * f p = e * g p := by
  induction p using LaurentPolynomial.induction_on with
  | h_C r => exact hc r
  | h_add ih jh => simp only [map_add, mul_add, ih, jh]
  | h_C_mul_T n r ih =>
    rw [T_add, ← mul_assoc]
    simpa only [map_mul] using weighted_mul _ _ _ _ _ ih hp
  | h_C_mul_T_Z n r ih =>
    rw [sub_eq_add_neg, T_add, ← mul_assoc]
    simpa only [map_mul] using weighted_mul _ _ _ _ _ ih hn

/-- Both coefficient maps and Laurent units can vary modulo the same annihilator. -/
theorem weighted_eval₂ (e : B) (f g : R →+* B) (u v : Bˣ)
    (hc : ∀ r, e * f r = e * g r) (hu : e * u.val = e * v.val)
    (p : R[T;T⁻¹]) : e * eval₂ f u p = e * eval₂ g v p := by
  apply weighted_hom e _ _ _ _ _ p
  · simpa only [eval₂_C] using hc
  · simpa only [eval₂_T, zpow_one] using hu
  · simpa only [eval₂_T, zpow_neg_one] using weighted_inv e u v hu

variable [Algebra R B]

/-- A Laurent polynomial cannot distinguish units equal modulo the weight's annihilator. -/
theorem weighted_evalUnit (e : B) (u v : Bˣ) (hu : e * u.val = e * v.val)
    (p : R[T;T⁻¹]) : e * evalUnit u p = e * evalUnit v p :=
  weighted_eval₂ e _ _ u v (fun _ ↦ rfl) hu p

/-- Weighted two-variable evaluation respects weighted equality in each unit input. -/
theorem weighted_pairEval (e : B) (u u' v v' : Bˣ)
    (hu : e * u.val = e * u'.val) (hv : e * v.val = e * v'.val)
    (p : R[T;T⁻¹][T;T⁻¹]) : e * pairEval u v p = e * pairEval u' v' p :=
  weighted_eval₂ e _ _ v v' (weighted_evalUnit e u u' hu) hv p

end FLT.Mazur.LaurentWeightedEvaluation
