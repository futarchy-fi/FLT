/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarGeometricPointTests
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Canonical geometric tests at an unchanged scalar prime

Construct one algebraically closed coefficient field at each original prime.
Field-valued points in this fixed field detect the entire exact original
fiber, including nonclosed fiber primes. No chosen scalar branch is needed.
-/

@[expose] public noncomputable section
universe u
namespace FLT.Mazur.ScalarTestLocalization
variable {R B : Type u} [CommRing R] [CommRing B]
  (s : R →+* B) (P : PrimeSpectrum R)
local notation "K" => AlgebraicClosure P.asIdeal.ResidueField

/-- Vanishing at all points in one fixed algebraic closure of the original residue field. -/
@[irreducible] def residueGeometricTest (b : B) : Prop :=
  ∀ v : B →+* K, v.comp s = algebraMap R K → v b = 0

/-- Expose the geometric test without any rank or neighborhood conclusion. -/
theorem residueGeometricTest_iff (b : B) :
    residueGeometricTest s P b ↔
      ∀ v : B →+* K, v.comp s = algebraMap R K → v b = 0 := by
  rw [residueGeometricTest]

omit s in
/-- The constructed algebraically closed field retains exactly the original prime. -/
theorem algebraicClosure_residue_center :
    PrimeSpectrum.comap (algebraMap R K) (⊥ : PrimeSpectrum K) = P := by
  apply PrimeSpectrum.ext
  ext r
  change algebraMap R K r = 0 ↔ r ∈ P.asIdeal
  rw [IsScalarTower.algebraMap_apply R P.asIdeal.ResidueField K,
    map_eq_zero, Ideal.algebraMap_residueField_eq_zero]

/-- Finite type turns canonical geometric values into all exact original fiber tests. -/
theorem residueGeometricTest_iff_original_fiber (hs : s.FiniteType) (b : B) :
    residueGeometricTest s P b ↔
      ∀ q : PrimeSpectrum B, PrimeSpectrum.comap s q = P → b ∈ q.asIdeal := by
  let _ := s.toAlgebra
  let _ : Algebra.FiniteType R B := RingHom.finiteType_algebraMap.mp hs
  rw [residueGeometricTest_iff]
  have h := original_fiber_test_iff_point_values (R := R) K b
  rw [algebraicClosure_residue_center] at h
  refine Iff.trans ?_ h.symm
  constructor
  · intro hv v
    exact hv v.toRingHom v.comp_algebraMap
  · intro hv v he
    exact hv { __ := v, commutes' := DFunLike.congr_fun he }

/-- Failure of an original exact test constructs a point over the canonical residue closure. -/
theorem exists_residue_geometric_failure (hs : s.FiniteType) (b : B)
    (q : PrimeSpectrum B) (hq : PrimeSpectrum.comap s q = P) (hb : b ∉ q.asIdeal) :
    ∃ v : B →+* K, v.comp s = algebraMap R K ∧ v b ≠ 0 := by
  have hn : ¬ residueGeometricTest s P b :=
    fun h ↦ hb ((residueGeometricTest_iff_original_fiber s P hs b).mp h q hq)
  rw [residueGeometricTest_iff] at hn
  simpa only [not_forall, not_imp, exists_prop] using hn

end FLT.Mazur.ScalarTestLocalization
