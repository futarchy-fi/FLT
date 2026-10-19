/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarTensorExactFibers
public import FLT.Mazur.OriginalScalarFiberFiniteEquations
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Exact original tests from geometric coefficient fibers

A field over the original scalar ring detects precisely its kernel fiber.
Nilpotence on that field tensor constructs original equations modulo the
original prime. These are fiber equations, not neighborhood annihilation.
-/

@[expose] public noncomputable section
open TensorProduct
universe u
namespace FLT.Mazur.ScalarTestLocalization
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
  (K : Type u) [Field K] [Algebra R K]
local notation "B'" => K ⊗[R] B
local notation "j" => Algebra.TensorProduct.includeRight (R := R) (A := K) (B := B)
local notation "center" => PrimeSpectrum.comap (algebraMap R K) (⊥ : PrimeSpectrum K)

/-- Nilpotence after any field extension detects every point of the exact original fiber. -/
theorem geometric_nilpotent_iff_fiber (b : B) :
    IsNilpotent (j b) ↔ ∀ q : PrimeSpectrum B,
      PrimeSpectrum.comap (algebraMap R B) q = center → b ∈ q.asIdeal := by
  rw [original_fiber_test_iff_tensor K (⊥ : PrimeSpectrum K) b]
  rw [← mem_nilradical, PrimeSpectrum.nilradical_eq_iInf, Ideal.mem_iInf]
  exact ⟨fun h z _ ↦ h z, fun h z ↦ h z (Subsingleton.elim _ _)⟩

/-- Geometric nilpotence clears to an original equation modulo the original scalar prime. -/
theorem geometric_nilpotent_iff_original_power (b : B) :
    IsNilpotent (j b) ↔ ∃ (n : ℕ) (r : R), r ∉ (center).asIdeal ∧
      algebraMap R B r * b ^ n ∈ (center).asIdeal.map (algebraMap R B) := by
  rw [geometric_nilpotent_iff_fiber]
  have he (q : PrimeSpectrum B) :
      PrimeSpectrum.comap (algebraMap R B) q = center ↔
        q.asIdeal.comap (algebraMap R B) = (center).asIdeal := PrimeSpectrum.ext_iff
  simp_rw [he]
  exact OriginalScalarFiberRadical.forall_fiber_primes_iff_power _ _ b

/-- Finite geometric tests construct one original denominator, without a flat field map. -/
theorem geometric_tests_common_denominator (a : Finset B)
    (h : ∀ b ∈ a, IsNilpotent (j b)) :
    ∃ r : R, r ∉ (center).asIdeal ∧ ∀ b ∈ a, ∃ n : ℕ,
      algebraMap R B r * b ^ n ∈ (center).asIdeal.map (algebraMap R B) := by
  apply OriginalScalarFiberRadical.exists_common_power_denominator
    (algebraMap R B) (center).asIdeal a
  intro b hb
  exact (geometric_nilpotent_iff_original_power K b).mp (h b hb)

/-- The canonical residue field has exactly the prescribed original scalar center. -/
theorem residueField_center (P : PrimeSpectrum R) :
    PrimeSpectrum.comap (algebraMap R P.asIdeal.ResidueField)
      (⊥ : PrimeSpectrum P.asIdeal.ResidueField) = P := by
  apply PrimeSpectrum.ext
  exact P.asIdeal.ker_algebraMap_residueField

/-- The canonical full residue tensor detects original exact-fiber vanishing. -/
theorem residue_nilpotent_iff_fiber (P : PrimeSpectrum R) (b : B) :
    IsNilpotent (Algebra.TensorProduct.includeRight
      (R := R) (A := P.asIdeal.ResidueField) (B := B) b) ↔
    ∀ q : PrimeSpectrum B, PrimeSpectrum.comap (algebraMap R B) q = P → b ∈ q.asIdeal := by
  rw [geometric_nilpotent_iff_fiber, residueField_center]

end FLT.Mazur.ScalarTestLocalization
