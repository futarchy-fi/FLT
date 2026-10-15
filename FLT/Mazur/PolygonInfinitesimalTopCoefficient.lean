/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonInfinitesimalRestrictionKernel
public import FLT.Mazur.PolygonInfinitesimalStageReduction

/-!
# Canonical coefficients of the finite smoothing base

Polynomial remainders give coefficient functionals on the actual truncated
base. The top coefficient recovers exactly the scalar in its adjacent kernel.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
variable (R : Type*) [CommRing R] (m : ℕ)

/-- The coefficient of q^j in the canonical representative of a stage element. -/
def stageCoeff (j : ℕ) : Ring R m →ₗ[R] R :=
  (Polynomial.lcoeff R j).comp (AdjoinRoot.modByMonicHom (monic_X.pow (m + 1)))

/-- Below the truncation bound, coefficients may be read from any representative. -/
theorem stageCoeff_mk (j : ℕ) (hj : j ≤ m) (p : R[X]) :
    stageCoeff R m j (AdjoinRoot.mk _ p) = p.coeff j := by
  change (p %ₘ (X ^ (m + 1))).coeff j = p.coeff j
  rw [modByMonic_eq_sub_mul_div, coeff_sub, coeff_X_pow_mul']
  simp only [show ¬ m + 1 ≤ j by omega, ite_false, sub_zero]

/-- The top coefficient of q^m times an element is its closed reduction. -/
theorem stageCoeff_top_mul (a : Ring R m) :
    stageCoeff R m m (parameter R m ^ m * a) = reduction R m a := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
  change stageCoeff R m m ((AdjoinRoot.mk _) X ^ m * AdjoinRoot.mk _ p) = _
  rw [← map_pow, ← map_mul, stageCoeff_mk R m m le_rfl, reduction_mk]
  simpa only [zero_add] using coeff_X_pow_mul p m 0

/-- The top parameter power forgets every positive-degree coefficient of its other factor. -/
theorem parameter_top_mul_reduction (a : Ring R m) :
    parameter R m ^ m * a =
      parameter R m ^ m * algebraMap R (Ring R m) (reduction R m a) := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
  rw [reduction_mk]
  have hd : X ∣ p - C (p.coeff 0) := by
    apply X_dvd_iff.mpr
    simp only [coeff_sub, coeff_C_zero, sub_self]
  obtain ⟨b, hb⟩ := hd
  apply sub_eq_zero.mp
  rw [← mul_sub_left_distrib]
  change AdjoinRoot.mk _ X ^ m * (AdjoinRoot.mk _ p - AdjoinRoot.mk _ (C (p.coeff 0))) = 0
  rw [← map_sub, hb, map_mul, ← mul_assoc]
  change parameter R m ^ m * parameter R m * _ = 0
  rw [← pow_succ, parameter_pow, zero_mul]

/-- A top-order kernel element is reconstructed from its canonical top coefficient. -/
theorem restriction_kernel_top (a : Ring R (m + 1)) (ha : restriction R m a = 0) :
    a = parameter R (m + 1) ^ (m + 1) *
      algebraMap R (Ring R (m + 1)) (stageCoeff R (m + 1) (m + 1) a) := by
  obtain ⟨b, rfl⟩ := (restriction_eq_zero_iff R m a).mp ha
  rw [stageCoeff_top_mul, parameter_top_mul_reduction]

/-- Vanishing of the top coefficient detects zero inside the actual adjacent kernel. -/
theorem restriction_kernel_eq_zero_iff (a : Ring R (m + 1))
    (ha : restriction R m a = 0) :
    a = 0 ↔ stageCoeff R (m + 1) (m + 1) a = 0 := by
  constructor
  · rintro rfl
    exact map_zero _
  · intro hc
    rw [restriction_kernel_top R m a ha, hc, map_zero, mul_zero]

end FLT.Mazur.PolygonInfinitesimalStages
