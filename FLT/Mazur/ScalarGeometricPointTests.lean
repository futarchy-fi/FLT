/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarGeometricFiberTests
public import FLT.Mazur.AffineRationalNonvanishing
public import Mathlib.RingTheory.FiniteStability

/-!
# Original fiber equations from geometric point values

Finite type makes algebraically closed field-valued points detect nilpotence
on the full geometric fiber. The tensor universal property expresses these
as maps from the original coefficient algebra, so geometry need not quantify
over tensor primes. Nonvanishing constructs an actual geometric point.
-/

@[expose] public noncomputable section
open TensorProduct
universe u
namespace FLT.Mazur.ScalarTestLocalization
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
  [Algebra.FiniteType R B] (K : Type u) [Field K] [IsAlgClosed K] [Algebra R K]
local notation "B'" => K ⊗[R] B
local notation "j" => Algebra.TensorProduct.includeRight (R := R) (A := K) (B := B)
local notation "center" => PrimeSpectrum.comap (algebraMap R K) (⊥ : PrimeSpectrum K)

/-- A nonnilpotent geometric test constructs a field-valued point of the original algebra. -/
theorem exists_geometric_test_point (b : B) (hb : ¬ IsNilpotent (j b)) :
    ∃ v : B →ₐ[R] K, v b ≠ 0 := by
  obtain ⟨v, hv⟩ := AffineRationalNonvanishing.exists_point (k := K) (j b) hb
  exact ⟨(AlgHom.liftEquiv R K B K).symm v, hv⟩

/-- Geometric points detect full tensor nilpotence, retaining infinitesimal coefficients. -/
theorem geometric_nilpotent_iff_point_values (b : B) :
    IsNilpotent (j b) ↔ ∀ v : B →ₐ[R] K, v b = 0 := by
  constructor
  · intro h v
    have hz := h.map (AlgHom.liftEquiv R K B K v)
    simpa only [Algebra.TensorProduct.includeRight_apply, AlgHom.liftEquiv_tmul,
      one_smul, isNilpotent_iff_eq_zero] using hz
  · intro h
    by_contra hn
    obtain ⟨v, hv⟩ := exists_geometric_test_point K b hn
    exact hv (h v)

/-- Geometric point values construct exact original tests at the unchanged scalar center. -/
theorem original_fiber_test_iff_point_values (b : B) :
    (∀ q : PrimeSpectrum B, PrimeSpectrum.comap (algebraMap R B) q = center →
      b ∈ q.asIdeal) ↔ ∀ v : B →ₐ[R] K, v b = 0 :=
  (geometric_nilpotent_iff_fiber K b).symm.trans
    (geometric_nilpotent_iff_point_values K b)

/-- Vanishing on geometric points produces one original denominator for finitely many tests. -/
theorem point_tests_common_denominator (a : Finset B)
    (h : ∀ v : B →ₐ[R] K, ∀ b ∈ a, v b = 0) :
    ∃ r : R, r ∉ (center).asIdeal ∧ ∀ b ∈ a, ∃ n : ℕ,
      algebraMap R B r * b ^ n ∈ (center).asIdeal.map (algebraMap R B) := by
  apply geometric_tests_common_denominator K a
  intro b hb
  exact (geometric_nilpotent_iff_point_values K b).mpr (fun v ↦ h v b hb)

end FLT.Mazur.ScalarTestLocalization
