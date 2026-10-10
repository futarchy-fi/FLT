/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXConicParameterSections
public import FLT.Mazur.WeierstrassModificationXFiberConicGeometry

/-!
# Each complete conic parameter meets incidence exactly at its origin

These full inverse-image formulas work for arbitrary coefficients and conic constant.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (a c : R) (ha : IsUnit a)

/-- Evaluation at the original parameter origin has precisely the origin ideal as kernel. -/
theorem conicParameterOrigin_ker :
    RingHom.ker (conicParameterOrigin c) = conicParameterOriginIdeal c := by
  ext z
  change conicParameterOrigin c z = 0 ↔ z ∈ conicParameterOriginIdeal c
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← (conicParameterOriginEquiv c).injective.eq_iff,
    map_zero, conicParameterOriginEquiv_mk]

/-- The entire parameter-origin section is exactly the zero locus of the parameter. -/
theorem conicParameterOrigin_range :
    Set.range (Spec.map (CommRingCat.ofHom (conicParameterOrigin c).toRingHom)) =
      PrimeSpectrum.zeroLocus (conicParameterOriginIdeal c) := by
  rw [← conicParameterOrigin_ker]
  exact range_comap_of_surjective _ _ (fun r => ⟨algebraMap R _ r,
    (conicParameterOrigin c).commutes r⟩)

/-- The full first parameter has no additional incidence points. -/
theorem conicFirstParameter_incidence_preimage :
    ((conicFirstParameterIso a c ha).inv ≫ conicFirstOpenImmersion a c ≫
        fiberConicImmersion a c) ⁻¹' Set.range (fiberIncidenceImmersion a c) =
      Set.range (Spec.map (CommRingCat.ofHom (conicParameterOrigin c).toRingHom)) := by
  rw [range_fiberIncidenceImmersion, conicParameterOrigin_range]
  change (PrimeSpectrum.comap ((conicFirstParameterEquiv a c ha).symm.toRingHom.comp
    ((algebraMap (ConicCoordinate a c) (ConicFirstOpen a c)).comp
      (fiberConicMap a c).toRingHom))) ⁻¹'
    PrimeSpectrum.zeroLocus (Ideal.span {fiberT a c}) = _
  rw [PrimeSpectrum.preimage_comap_zeroLocus, ← PrimeSpectrum.zeroLocus_span]
  congr 1
  refine congrArg (fun I : Ideal (ConicParameterOpen c) =>
    (I : Set (ConicParameterOpen c))) ?_
  rw [← Ideal.map_span, Ideal.span_eq, Ideal.map_span, Set.image_singleton]
  change Ideal.span {(conicFirstToParameter a c ha
    (algebraMap (ConicCoordinate a c) (ConicFirstOpen a c)
      (fiberConicMap a c (fiberT a c))))} = _
  rw [fiberConicMap_t, conicFirstToParameter_base, conicToParameter_t,
    conicInverseT_span a c ha]

/-- The opposite full parameter likewise meets incidence only at its own original origin. -/
theorem conicSecondParameter_incidence_preimage :
    ((conicSecondParameterIso a c ha).inv ≫ conicSecondOpenImmersion a c ≫
        fiberConicImmersion a c) ⁻¹' Set.range (fiberIncidenceImmersion a c) =
      Set.range (Spec.map (CommRingCat.ofHom (conicParameterOrigin c).toRingHom)) := by
  rw [range_fiberIncidenceImmersion, conicParameterOrigin_range]
  change (PrimeSpectrum.comap ((conicSecondParameterEquiv a c ha).symm.toRingHom.comp
    ((algebraMap (ConicCoordinate a c) (ConicSecondOpen a c)).comp
      (fiberConicMap a c).toRingHom))) ⁻¹'
    PrimeSpectrum.zeroLocus (Ideal.span {fiberT a c}) = _
  rw [PrimeSpectrum.preimage_comap_zeroLocus, ← PrimeSpectrum.zeroLocus_span]
  congr 1
  refine congrArg (fun I : Ideal (ConicParameterOpen c) =>
    (I : Set (ConicParameterOpen c))) ?_
  rw [← Ideal.map_span, Ideal.span_eq, Ideal.map_span, Set.image_singleton]
  change Ideal.span {((conicSecondParameterEquiv a c ha).symm
    (algebraMap (ConicCoordinate a c) (ConicSecondOpen a c)
      (fiberConicMap a c (fiberT a c))))} = _
  rw [fiberConicMap_t, conicSecondParameterEquiv_symm_t, conicInverseT_span (-a) c ha.neg]

end FLT.Mazur.WeierstrassModificationX
