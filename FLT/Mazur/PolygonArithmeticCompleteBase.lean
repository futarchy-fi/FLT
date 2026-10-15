/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PowerSeriesArithmeticCompletion
public import FLT.Mazur.SurjectiveKernelPushout

/-!
# The actual Cartesian coefficient square over a complete integral base

The integral evaluation t ↦ π takes the power-series parameter ideal onto
the original arithmetic ideal. Its finite quotients form genuine pushouts,
so the arithmetic stages are base changes along one complete-base map.
-/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace FLT.Mazur.PolygonArithmeticStages
universe u
open PolygonInfinitesimalStages
variable (A : Type u) [CommRing A] (π : A) [IsAdicComplete (ideal A π) A]

/-- The complete integral evaluation takes the actual parameter ideal to the original ideal. -/
theorem completeSpecialization_parameterIdeal :
    (parameterIdeal A).map (completeSpecialization A π).toRingHom = ideal A π := by
  rw [parameterIdeal, Ideal.map_span, Set.image_singleton]
  change Ideal.span {completeSpecialization A π PowerSeries.X} = _
  rw [completeSpecialization_X]
  rfl

/-- Every original ideal power is the image of the corresponding universal parameter power. -/
theorem completeSpecialization_parameterIdeal_pow (m : ℕ) :
    (parameterIdeal A ^ m).map (completeSpecialization A π).toRingHom = ideal A π ^ m := by
  rw [Ideal.map_pow, completeSpecialization_parameterIdeal]

/-- The specified complete evaluation and both finite coefficient maps commute. -/
theorem completeSpecialization_square (m : ℕ) :
    (Ideal.Quotient.mk (ideal A π ^ (m + 1))).comp (completeSpecialization A π).toRingHom =
      (specialization A π m).toRingHom.comp (seriesToStage A m).toRingHom := by
  ext f
  exact completeSpecialization_stage A π m f

/-- The common finite evaluation kills exactly the sum of the two original kernels. -/
theorem completeSpecialization_square_ker (m : ℕ) :
    RingHom.ker ((Ideal.Quotient.mk (ideal A π ^ (m + 1))).comp
      (completeSpecialization A π).toRingHom) =
        RingHom.ker (completeSpecialization A π).toRingHom ⊔
          RingHom.ker (seriesToStage A m).toRingHom := by
  have hk : RingHom.ker ((Ideal.Quotient.mk (ideal A π ^ (m + 1))).comp
      (completeSpecialization A π).toRingHom) =
        (ideal A π ^ (m + 1)).comap (completeSpecialization A π).toRingHom := by
    ext f
    exact Ideal.Quotient.eq_zero_iff_mem
  rw [hk, ← completeSpecialization_parameterIdeal_pow A π (m + 1),
    Ideal.comap_map_of_surjective (completeSpecialization A π).toRingHom
      (completeSpecialization_surjective A π),
    seriesToStage_ker, RingHom.ker_eq_comap_bot, sup_comm]

/-- The complete integral base map has exactly the prescribed finite coefficient pushouts. -/
theorem completeSpecialization_isPushout (m : ℕ) :
    IsPushout (CommRingCat.ofHom (completeSpecialization A π).toRingHom)
      (CommRingCat.ofHom (seriesToStage A m).toRingHom)
      (CommRingCat.ofHom (Ideal.Quotient.mk (ideal A π ^ (m + 1))))
      (CommRingCat.ofHom (specialization A π m).toRingHom) := by
  apply SurjectiveKernelPushout.isPushout
  · exact completeSpecialization_surjective A π
  · exact seriesToStage_surjective A m
  · exact (Ideal.Quotient.mk_surjective).comp (completeSpecialization_surjective A π)
  · exact completeSpecialization_square A π m
  · exact completeSpecialization_square_ker A π m

end FLT.Mazur.PolygonArithmeticStages
