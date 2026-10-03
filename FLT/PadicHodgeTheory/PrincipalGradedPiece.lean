/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.RingTheory.Ideal.Span

/-! # The actual successive quotients of a principal filtration -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable {R : Type*} [CommRing R] [IsDomain R]

/-- The next principal power viewed as a submodule of the current principal ideal. -/
def principalGradedSubmodule (t : R) (n : ℕ) :
    Submodule R (Ideal.span {t ^ n}) :=
  (Ideal.span {t ^ (n + 1)}).comap (Ideal.span {t ^ n}).subtype

/-- The actual quotient of consecutive principal ideals. -/
abbrev PrincipalGradedPiece (t : R) (n : ℕ) :=
  (Ideal.span {t ^ n}) ⧸ principalGradedSubmodule t n

/-- Multiplication by the nonzero n-th power identifies its coefficients uniquely. -/
def principalPowerEquiv {t : R} (ht : t ≠ 0) (n : ℕ) : R ≃ₗ[R] Ideal.span {t ^ n} :=
  LinearEquiv.toSpanNonzeroSingleton R R (t ^ n) (pow_ne_zero n ht)

/-- The next ideal power corresponds exactly to coefficients divisible by t. -/
theorem principalGradedSubmodule_comap {t : R} (ht : t ≠ 0) (n : ℕ) :
    (principalGradedSubmodule t n).comap (principalPowerEquiv ht n).toLinearMap =
      Ideal.span {t} := by
  ext a
  change a * t ^ n ∈ Ideal.span {t ^ (n + 1)} ↔ a ∈ Ideal.span {t}
  simp only [Ideal.mem_span_singleton]
  rw [pow_succ, mul_comm a, mul_dvd_mul_iff_left (pow_ne_zero n ht)]

/-- Dividing by t^n identifies the actual graded quotient with the residue module. -/
def principalGradedEquiv {t : R} (ht : t ≠ 0) (n : ℕ) :
    (R ⧸ Ideal.span {t}) ≃ₗ[R] PrincipalGradedPiece t n :=
  Submodule.Quotient.equiv _ _ (principalPowerEquiv ht n) (by
    rw [← principalGradedSubmodule_comap ht n]
    exact Submodule.map_comap_eq_of_surjective (principalPowerEquiv ht n).surjective _)

/-- A residue representative maps to its multiple of t^n in the actual graded quotient. -/
theorem principalGradedEquiv_mk {t : R} (ht : t ≠ 0) (n : ℕ) (a : R) :
    principalGradedEquiv ht n (Submodule.Quotient.mk a) =
      (principalGradedSubmodule t n).mkQ (principalPowerEquiv ht n a) := rfl

end PadicHodgeTheory
