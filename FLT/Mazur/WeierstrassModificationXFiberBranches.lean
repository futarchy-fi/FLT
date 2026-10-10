/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFiberNormalForm
public import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
# The three actual branches before the middle depth

The three-line fiber has the original incidence component and the two
oriented tangent components. Every prime belongs to one of them. The tangent
components are disjoint when their original coefficient difference is a unit.
The polynomial branch maps below are surjective and retain the coordinates.
-/

@[expose] public noncomputable section

open Polynomial

namespace FLT.Mazur.WeierstrassModificationX

variable {R : Type*} [CommRing R] (a : R)

/-- Before the middle depth the full horizontal fiber equation is a three-factor product. -/
theorem fiber_lines_relation :
    fiberT a 0 * fiberV a 0 * (fiberV a 0 + algebraMap R _ a) = 0 := by
  simpa only [map_zero, zero_mul, sub_zero, mul_assoc] using fiber_relation a (0 : R)

/-- Every prime of the entire three-line fiber lies on one of its original branches. -/
theorem fiber_prime_branches (p : PrimeSpectrum (FiberCoordinate a 0)) :
    fiberT a 0 ∈ p.asIdeal ∨ fiberV a 0 ∈ p.asIdeal ∨
      fiberV a 0 + algebraMap R _ a ∈ p.asIdeal := by
  have h : fiberT a 0 * fiberV a 0 * (fiberV a 0 + algebraMap R _ a) ∈ p.asIdeal := by
    rw [fiber_lines_relation]
    exact p.asIdeal.zero_mem
  rcases p.isPrime.mem_or_mem h with h | h
  · rcases p.isPrime.mem_or_mem h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- The actual two tangent factors are coprime when the original tangent coefficient is a unit. -/
theorem fiber_tangent_coprime (ha : IsUnit a) :
    IsCoprime (fiberV a (0 : R)) (fiberV a 0 + algebraMap R _ a) := by
  obtain ⟨u, rfl⟩ := ha
  refine ⟨-algebraMap R _ (↑u⁻¹ : R), algebraMap R _ (↑u⁻¹ : R), ?_⟩
  have hi : algebraMap R (FiberCoordinate (↑u : R) 0) (↑u⁻¹ : R) *
      algebraMap R _ (↑u : R) = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  linear_combination hi

/-- The two original tangent components never meet, even at a nonclosed prime. -/
theorem fiber_tangent_branches_disjoint (ha : IsUnit a)
    (p : PrimeSpectrum (FiberCoordinate a 0)) :
    ¬ (fiberV a 0 ∈ p.asIdeal ∧ fiberV a 0 + algebraMap R _ a ∈ p.asIdeal) := by
  rintro ⟨h0, h1⟩
  have hu : algebraMap R (FiberCoordinate a 0) a ∈ p.asIdeal := by
    simpa only [add_sub_cancel_left] using p.asIdeal.sub_mem h1 h0
  exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hu (ha.map (algebraMap R _)))

/-- The incidence-zero component keeps the original slope as its affine-line coordinate. -/
def fiberCentralLine : FiberCoordinate a 0 →ₐ[R] R[X] :=
  fiberEvaluation a 0 0 X (by simp)

/-- The first tangent component keeps the incidence ratio as its affine-line coordinate. -/
def fiberFirstLine : FiberCoordinate a 0 →ₐ[R] R[X] :=
  fiberEvaluation a 0 X 0 (by simp)

/-- The second oriented tangent component has the original slope -a. -/
def fiberSecondLine : FiberCoordinate a 0 →ₐ[R] R[X] :=
  fiberEvaluation a 0 X (-C a) (by simp)

/-- The incidence-zero line map preserves its free slope coordinate. -/
@[simp] theorem fiberCentralLine_v : fiberCentralLine a (fiberV a 0) = X :=
  fiberEvaluation_v _ _ _ _ _

/-- The first tangent line map preserves its free incidence coordinate. -/
@[simp] theorem fiberFirstLine_t : fiberFirstLine a (fiberT a 0) = X :=
  fiberEvaluation_t _ _ _ _ _

/-- The second tangent line map preserves its free incidence coordinate. -/
@[simp] theorem fiberSecondLine_t : fiberSecondLine a (fiberT a 0) = X :=
  fiberEvaluation_t _ _ _ _ _

/-- Every polynomial slope function comes from the actual incidence-zero branch. -/
theorem fiberCentralLine_surjective : Function.Surjective (fiberCentralLine a) := by
  intro p
  refine ⟨aeval (fiberV a 0) p, ?_⟩
  rw [← aeval_algHom_apply, fiberCentralLine_v]
  exact aeval_X_left_apply p

/-- Every polynomial incidence function comes from the actual first tangent branch. -/
theorem fiberFirstLine_surjective : Function.Surjective (fiberFirstLine a) := by
  intro p
  refine ⟨aeval (fiberT a 0) p, ?_⟩
  rw [← aeval_algHom_apply, fiberFirstLine_t]
  exact aeval_X_left_apply p

/-- Every polynomial incidence function comes from the actual second tangent branch. -/
theorem fiberSecondLine_surjective : Function.Surjective (fiberSecondLine a) := by
  intro p
  refine ⟨aeval (fiberT a 0) p, ?_⟩
  rw [← aeval_algHom_apply, fiberSecondLine_t]
  exact aeval_X_left_apply p

end FLT.Mazur.WeierstrassModificationX
