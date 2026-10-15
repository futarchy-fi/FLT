/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticResidueFiber

/-!
# Nilpotent residue fibers of the original arithmetic stages

When the original parameter generates the maximal ideal, every element of
the finite residue kernel has the explicit exponent m + 1. Thus the original
residue polygon covers the entire underlying space of each arithmetic stage.
No coefficient field in the integral base is required.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
namespace FLT.Mazur.PolygonArithmeticStages
universe u
variable (A : Type u) [CommRing A] [IsLocalRing A] (π : A)
  (hgen : maximalIdeal A = ideal A π)

include hgen in
/-- A generator of the maximal ideal vanishes under the original residue map. -/
theorem parameter_residue_zero : algebraMap A (ResidueField A) π = 0 := by
  change residue A π = 0
  rw [residue_eq_zero_iff, hgen]
  exact Ideal.subset_span (Set.mem_singleton π)

variable (hπ : algebraMap A (ResidueField A) π = 0) (m : ℕ)

include hgen in
/-- The original residue kernel has an explicit uniform nilpotence exponent. -/
theorem residueMap_kernel_pow (z : Quotient A π m) (hz : residueMap A π hπ m z = 0) :
    z ^ (m + 1) = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  change residue A a = 0 at hz
  rw [residue_eq_zero_iff, hgen, ideal, Ideal.mem_span_singleton] at hz
  obtain ⟨b, rfl⟩ := hz
  rw [map_mul, mul_pow]
  change parameter A π m ^ (m + 1) * _ = 0
  rw [parameter_pow, zero_mul]

include hgen in
/-- The finite arithmetic residue kernel is contained in the nilradical. -/
theorem residueMap_kernel_le_nilradical :
    RingHom.ker (residueMap A π hπ m) ≤ nilradical (Quotient A π m) := by
  intro z hz
  exact mem_nilradical.mpr ⟨m + 1, residueMap_kernel_pow A π hgen hπ m z hz⟩

include hgen in
/-- The actual residue coefficient inclusion is surjective on prime spectra. -/
theorem residueBase_surjective : Surjective (residueBase A π hπ m) := by
  constructor
  change Function.Surjective (PrimeSpectrum.comap (residueMap A π hπ m))
  rw [← Set.range_eq_univ, range_comap_of_surjective _ _ (residueMap_surjective A π hπ m)]
  exact (PrimeSpectrum.zeroLocus_eq_univ_iff _).mpr
    (residueMap_kernel_le_nilradical A π hgen hπ m)

variable (n : ℕ) (h : 2 ≤ n)

/-- The original residue polygon is a closed subscheme of the whole arithmetic family. -/
instance residueFiberInclusion_isClosedImmersion :
    IsClosedImmersion (residueFiberInclusion A π hπ m n h) :=
  MorphismProperty.of_isPullback (residueFiberInclusion_isPullback A π hπ m n h).flip
    inferInstance

include hgen in
/-- The original residue polygon covers every point of the arithmetic thickening. -/
theorem residueFiberInclusion_surjective :
    Surjective (residueFiberInclusion A π hπ m n h) := by
  let _ := residueBase_surjective A π hgen hπ m
  exact MorphismProperty.of_isPullback
    (residueFiberInclusion_isPullback A π hπ m n h).flip inferInstance

end FLT.Mazur.PolygonArithmeticStages
