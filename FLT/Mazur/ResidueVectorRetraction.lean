/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
# Retractions from nonzero residue vectors

If a coordinate vector is nonzero in every prime residue field, its
coordinates generate the unit ideal. A finite linear combination then
constructs an actual retraction of the line it generates.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ResidueVectorRetraction
universe u v
variable {R : Type u} [CommRing R] {ι : Type v} (v : ι → R)

/-- Fiberwise nonzero coordinate vectors generate the unit ideal. -/
lemma span_eq_top_of_residue_ne_zero
    (h : ∀ p : PrimeSpectrum R, (fun i ↦ algebraMap R p.asIdeal.ResidueField (v i)) ≠ 0) :
    Ideal.span (Set.range v) = ⊤ := by
  by_contra hn
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (Ideal.span (Set.range v)) hn
  let _ := hm
  apply h ⟨m, inferInstance⟩
  funext i
  exact m.algebraMap_residueField_eq_zero.mpr (hle (Ideal.subset_span ⟨i, rfl⟩))

/-- A fiberwise nonzero vector admits a linear functional taking value one. -/
lemma exists_functional_of_residue_ne_zero
    (h : ∀ p : PrimeSpectrum R, (fun i ↦ algebraMap R p.asIdeal.ResidueField (v i)) ≠ 0) :
    ∃ φ : (ι → R) →ₗ[R] R, φ v = 1 := by
  have hs : Submodule.span R (Set.range v) = ⊤ := span_eq_top_of_residue_ne_zero v h
  obtain ⟨a, ha⟩ := ((span_range_eq_top_iff_surjective_finsuppLinearCombination R).mp hs) 1
  refine ⟨Finsupp.linearCombination R (fun i ↦ LinearMap.proj i) a, ?_⟩
  simpa only [Finsupp.linearCombination_apply, Finsupp.sum, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.proj_apply] using ha

/-- The functional splits the original scalar-multiple map into the coordinate module. -/
lemma exists_retraction_of_residue_ne_zero
    (h : ∀ p : PrimeSpectrum R, (fun i ↦ algebraMap R p.asIdeal.ResidueField (v i)) ≠ 0) :
    ∃ φ : (ι → R) →ₗ[R] R,
      φ.comp (LinearMap.toSpanSingleton R (ι → R) v) = LinearMap.id := by
  obtain ⟨φ, hφ⟩ := exists_functional_of_residue_ne_zero v h
  refine ⟨φ, LinearMap.ext fun r ↦ ?_⟩
  change φ (r • v) = r
  rw [map_smul, hφ, smul_eq_mul, mul_one]

end FLT.Mazur.ResidueVectorRetraction
