/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonPowerSeriesBase

/-!
# Integral coefficients for the arithmetic smoothing stages

The original ring, rather than its residue field, supplies the coefficients.
At every finite order the universal smoothing parameter specializes to the
original element π modulo its corresponding power. These maps preserve
constants and commute with the original stage restrictions.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.PolygonArithmeticStages
open PolygonInfinitesimalStages Polynomial
variable (A : Type*) [CommRing A] (π : A)

/-- The ideal defining the arithmetic thickenings. -/
def ideal : Ideal A := Ideal.span {π}

/-- The actual arithmetic coefficient ring at order m. -/
abbrev Quotient (m : ℕ) := A ⧸ ideal A π ^ (m + 1)

/-- The image of the original uniformizing element. -/
def parameter (m : ℕ) : Quotient A π m := algebraMap A _ π

/-- The arithmetic parameter has the required finite-order nilpotence. -/
theorem parameter_pow (m : ℕ) : parameter A π m ^ (m + 1) = 0 := by
  change (Ideal.Quotient.mk _ π) ^ (m + 1) = 0
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, ideal, Ideal.span_singleton_pow]
  exact Ideal.subset_span (Set.mem_singleton _)

/-- Specialize the universal truncated parameter to the original arithmetic parameter. -/
def specialization (m : ℕ) : Ring A m →ₐ[A] Quotient A π m :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId A _) (parameter A π m) (by
    simpa only [eval₂_pow, eval₂_X] using parameter_pow A π m)

/-- Specialization preserves the specified smoothing parameter. -/
@[simp] theorem specialization_parameter (m : ℕ) :
    specialization A π m (PolygonInfinitesimalStages.parameter A m) = parameter A π m :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

/-- The original constants already surject onto each arithmetic coefficient ring. -/
theorem specialization_surjective (m : ℕ) : Function.Surjective (specialization A π m) := by
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨algebraMap A _ a, (specialization A π m).commutes a⟩

/-- The actual coefficient restriction on consecutive arithmetic thickenings. -/
def restriction (m : ℕ) : Quotient A π (m + 1) →ₐ[A] Quotient A π m :=
  Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right (Nat.le_succ (m + 1)))

/-- The original uniformizer is unchanged by restriction. -/
@[simp] theorem restriction_parameter (m : ℕ) :
    restriction A π m (parameter A π (m + 1)) = parameter A π m :=
  (restriction A π m).commutes π

/-- The arithmetic specializations commute with the original universal restrictions. -/
theorem restriction_specialization (m : ℕ) :
    (restriction A π m).comp (specialization A π (m + 1)) =
      (specialization A π m).comp (PolygonInfinitesimalStages.restriction A m) := by
  apply AdjoinRoot.algHom_ext
  change restriction A π m
      (specialization A π (m + 1) (PolygonInfinitesimalStages.parameter A (m + 1))) =
    specialization A π m (PolygonInfinitesimalStages.restriction A m
      (PolygonInfinitesimalStages.parameter A (m + 1)))
  rw [specialization_parameter, restriction_parameter,
    PolygonInfinitesimalStages.restriction_parameter, specialization_parameter]

/-- Evaluation of power series at π on the actual finite arithmetic thickening. -/
def seriesSpecialization (m : ℕ) : PowerSeries A →ₐ[A] Quotient A π m :=
  (specialization A π m).comp (seriesToStage A m)

/-- The complete-base parameter specializes to the original element, at every order. -/
@[simp] theorem seriesSpecialization_X (m : ℕ) :
    seriesSpecialization A π m PowerSeries.X = parameter A π m := by
  rw [seriesSpecialization, AlgHom.comp_apply, seriesToStage_X, specialization_parameter]

/-- The actual finite power-series evaluations are compatible at every smaller order. -/
theorem seriesSpecialization_compatible {a b : ℕ} (hab : a ≤ b) :
    (Ideal.Quotient.factorₐ A
      (Ideal.pow_le_pow_right (Nat.add_le_add_right hab 1))).comp
        (seriesSpecialization A π b) = seriesSpecialization A π a := by
  apply PowerSeriesNilpotentHom.ext
  · change IsNilpotent (Ideal.Quotient.factorₐ A
      (Ideal.pow_le_pow_right (Nat.add_le_add_right hab 1))
      (seriesSpecialization A π b PowerSeries.X))
    rw [seriesSpecialization_X]
    change IsNilpotent (Ideal.Quotient.factorₐ A
      (Ideal.pow_le_pow_right (Nat.add_le_add_right hab 1)) (algebraMap A _ π))
    rw [AlgHom.commutes]
    exact ⟨a + 1, parameter_pow A π a⟩
  · change Ideal.Quotient.factorₐ A
      (Ideal.pow_le_pow_right (Nat.add_le_add_right hab 1))
        (seriesSpecialization A π b PowerSeries.X) = _
    rw [seriesSpecialization_X, seriesSpecialization_X]
    exact (Ideal.Quotient.factorₐ A
      (Ideal.pow_le_pow_right (Nat.add_le_add_right hab 1))).commutes π

end FLT.Mazur.PolygonArithmeticStages
