/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonInfinitesimalStageRestriction
public import FLT.Mazur.PolygonStageCoefficientKernel

/-!
# Adjacent polygon stages are nilpotent closed immersions

The actual adjacent coefficient map is a surjection with nilpotent kernel.
Its cartesian polygon transition is therefore a surjective closed immersion.
This retains the original transition map needed for line-sheaf reduction.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

variable (R : Type*) [CommRing R] (m : ℕ)

/-- Every element of the adjacent coefficient kernel is square-zero. -/
theorem restriction_kernel_square (z : Ring R (m + 1)) (hz : restriction R m z = 0) :
    z ^ 2 = 0 := by
  obtain ⟨w, rfl⟩ := (restriction_eq_zero_iff R m z).mp hz
  rw [mul_pow, ← pow_mul]
  have he : (m + 1) * 2 = (m + 1 + 1) + m := by omega
  rw [he, pow_add (parameter R (m + 1)), parameter_pow, zero_mul, zero_mul]

/-- The adjacent coefficient kernel lies in the nilradical. -/
theorem restriction_kernel_le_nilradical :
    RingHom.ker (restriction R m).toRingHom ≤ nilradical (Ring R (m + 1)) := by
  intro z hz
  exact mem_nilradical.mpr ⟨2, restriction_kernel_square R m z hz⟩

/-- Adjacent coefficient spectra are related by the actual closed immersion. -/
instance baseRestriction_isClosedImmersion : IsClosedImmersion (baseRestriction R m) :=
  IsClosedImmersion.spec_of_surjective _ (restriction_surjective R m)

/-- Adjacent coefficient spectra have the same underlying support. -/
instance baseRestriction_surjective : Surjective (baseRestriction R m) := by
  constructor
  change Function.Surjective (PrimeSpectrum.comap (restriction R m).toRingHom)
  rw [← Set.range_eq_univ, range_comap_of_surjective _ _ (restriction_surjective R m)]
  exact (PrimeSpectrum.zeroLocus_eq_univ_iff _).mpr (restriction_kernel_le_nilradical R m)

variable (n : ℕ) (h : 2 ≤ n)

/-- The actual adjacent family transition is a closed immersion. -/
instance stageRestriction_isClosedImmersion : IsClosedImmersion (stageRestriction R m n h) :=
  MorphismProperty.of_isPullback (stageRestriction_isPullback R m n h).flip inferInstance

/-- Adjacent polygon stages have the same underlying support. -/
instance stageRestriction_surjective : Surjective (stageRestriction R m n h) :=
  MorphismProperty.of_isPullback (stageRestriction_isPullback R m n h).flip inferInstance

end FLT.Mazur.PolygonInfinitesimalStages
