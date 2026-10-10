/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXConicOverlapGeometry

/-!
# The original coordinates of the full conic parameter overlap maps

The two scheme projections are the spectra of the actual parameter algebra
maps. Their coordinates satisfy c*z₁*z₂=1 after every algebra extension,
with the original tangent ordering retained.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (a c : R) (ha : IsUnit a)
local notation "B" => ConicParameterOverlap a c
local notation "P" => ConicParameterOpen c

/-- The first full rational parameter algebra map into the original overlap. -/
def conicOverlapFirstParameterHom : P →ₐ[R] B :=
  (Algebra.algHom R (ConicFirstOpen a c) B).comp
    (conicFirstParameterEquiv a c ha).toAlgHom

/-- The second full rational parameter algebra map into that same overlap. -/
def conicOverlapSecondParameterHom : P →ₐ[R] B :=
  (conicSecondToOverlap a c).comp (conicSecondParameterEquiv a c ha).toAlgHom

/-- The first scheme projection retains the full first parameter algebra map. -/
theorem conicOverlapFirstParameterMap_eq_spec :
    conicOverlapFirstParameterMap a c ha =
      Spec.map (CommRingCat.ofHom (conicOverlapFirstParameterHom a c ha).toRingHom) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  rfl

/-- The second scheme projection retains the full opposite parameter algebra map. -/
theorem conicOverlapSecondParameterMap_eq_spec :
    conicOverlapSecondParameterMap a c ha =
      Spec.map (CommRingCat.ofHom (conicOverlapSecondParameterHom a c ha).toRingHom) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  rfl

/-- The first overlap map pulls back the polynomial coordinate to the original ratio t/(v+a). -/
theorem conicOverlapFirstParameterHom_z :
    conicOverlapFirstParameterHom a c ha (conicParameterZ c) =
      conicOverlapFirstParameter a c := by
  change algebraMap (ConicFirstOpen a c) B
    (conicParameterToFirst a c ha (conicParameterZ c)) = _
  rw [conicParameterToFirst_z]
  rfl

/-- The opposite overlap map pulls back the coordinate to the original ratio t/v. -/
theorem conicOverlapSecondParameterHom_z :
    conicOverlapSecondParameterHom a c ha (conicParameterZ c) =
      conicOverlapSecondParameter a c := by
  change conicSecondToOverlap a c (conicSecondParameterEquiv a c ha (conicParameterZ c)) = _
  rw [conicSecondParameterEquiv_z]
  rfl

/-- The full parameter maps have the reciprocal transition dictated by the original conic. -/
theorem conicOverlapParameterHom_relation :
    algebraMap R B c * conicOverlapFirstParameterHom a c ha (conicParameterZ c) *
      conicOverlapSecondParameterHom a c ha (conicParameterZ c) = 1 := by
  rw [conicOverlapFirstParameterHom_z, conicOverlapSecondParameterHom_z,
    conicOverlap_parameter_relation]

/-- Every coefficient-compatible algebra extension retains the ordered transition formula. -/
theorem conicOverlapParameterHom_relation_map {S : Type*} [CommRing S] [Algebra R S]
    (φ : B →ₐ[R] S) :
    algebraMap R S c * φ (conicOverlapFirstParameterHom a c ha (conicParameterZ c)) *
      φ (conicOverlapSecondParameterHom a c ha (conicParameterZ c)) = 1 := by
  simpa only [map_mul, map_one, AlgHom.commutes] using
    congrArg φ (conicOverlapParameterHom_relation a c ha)

end FLT.Mazur.WeierstrassModificationX
