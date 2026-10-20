/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonFiniteCoefficientCoordinates

/-!
# Exact recovery of the descended one-gon coordinate map

The entire square of coordinate rings commutes, not just its values at field
points. Injective coefficient inclusion also identifies the descended kernel
with the contraction of the original full ideal.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.OneGonFiniteCoefficientCoordinates

open WeierstrassIntegralChart OneGonSmoothing

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R G : Type*} [CommRing R] [AddCommMonoid G]
  (t : R) (j : Fin 3) (φ : Coordinate (equation t) j →ₐ[R] AddMonoidAlgebra R G)
  (s : Set R)

/-- The actual inclusion preserves the specified coefficient scalars. -/
theorem modelInclusion_scalar (a : modelRing t j φ s) :
    modelInclusion t j φ s (algebraMap _ _ a) =
      algebraMap R (AddMonoidAlgebra R G) (a : R) := by
  ext g
  simp [modelInclusion, CharacterFiniteCoefficientModel.inclusion]

/-- The chart coefficient map from the descended equation to the original one. -/
def modelChartMap : Coordinate (equation (modelParameter t j φ s)) j →+*
    Coordinate (equation t) j :=
  chartCoefficientRingMapTo (modelRing t j φ s).val.toRingHom
    (equation (modelParameter t j φ s)) j (equation t) (equation_map _ _)

/-- Every normalized coordinate is retained by the original chart comparison. -/
theorem modelChartMap_coord (i : Fin 3) :
    modelChartMap t j φ s (coord (equation (modelParameter t j φ s)) j i) =
      coord (equation t) j i := chartCoefficientRingMapTo_coord ..

/-- The original parameter inclusion is retained on all chart scalars. -/
theorem modelChartMap_scalar (a : modelRing t j φ s) :
    modelChartMap t j φ s (algebraMap _ _ a) =
      algebraMap R _ (a : R) := chartCoefficientRingMapTo_scalar ..

/-- The finite coefficient model recovers the full original algebra map. -/
theorem modelCoordinates_recovery :
    (modelInclusion t j φ s).comp (modelCoordinates t j φ s).toRingHom =
      φ.toRingHom.comp (modelChartMap t j φ s) := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro a
    change modelInclusion t j φ s (modelCoordinates t j φ s (algebraMap _ _ a)) =
      φ (modelChartMap t j φ s (algebraMap _ _ a))
    rw [AlgHom.commutes, modelInclusion_scalar, modelChartMap_scalar, AlgHom.commutes]
  · intro i
    change modelInclusion t j φ s (modelCoordinates t j φ s
      (coord (equation (modelParameter t j φ s)) j i)) =
        φ (modelChartMap t j φ s (coord (equation (modelParameter t j φ s)) j i))
    rw [modelChartMap_coord]
    rw [modelCoordinates, evaluation_coord]
    exact modelValues_recovery t j φ s i

/-- The descended full ideal is the contraction of the original full ideal. -/
theorem modelCoordinates_ker :
    RingHom.ker (modelCoordinates t j φ s).toRingHom =
      (RingHom.ker φ.toRingHom).comap (modelChartMap t j φ s) := by
  ext x
  change modelCoordinates t j φ s x = 0 ↔ φ (modelChartMap t j φ s x) = 0
  have h := RingHom.congr_fun (modelCoordinates_recovery t j φ s) x
  change modelInclusion t j φ s (modelCoordinates t j φ s x) =
    φ (modelChartMap t j φ s x) at h
  rw [← h]
  exact (map_eq_zero_iff (modelInclusion t j φ s)
    (CharacterFiniteCoefficientModel.inclusion_injective _ _)).symm

end FLT.Mazur.OneGonFiniteCoefficientCoordinates
