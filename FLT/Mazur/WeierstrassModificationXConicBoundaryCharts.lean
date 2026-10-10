/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXConicBoundaryOverlap

/-!
# Both full incidence-boundary inclusions into the ordered parameter charts

The original incidence open maps openly into each entire parameter chart.
Each inclusion retains all original conic functions and its ordered ratio.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (a c : R) (ha : IsUnit a) (hc : IsUnit c)
local notation "C₀" => ConicCoordinate a c
local notation "B" => ConicIncidenceOpen a c
local notation "P" => ConicParameterOpen c

/-- The full first parameter algebra restricted to the original incidence boundary. -/
def conicIncidenceFirstParameterHom : P →ₐ[R] B :=
  (conicFirstToIncidence a c hc).comp (conicFirstParameterEquiv a c ha).toAlgHom

/-- The full second parameter algebra restricted to the same original boundary. -/
def conicIncidenceSecondParameterHom : P →ₐ[R] B :=
  (conicSecondToIncidence a c hc).comp (conicSecondParameterEquiv a c ha).toAlgHom

/-- The first restriction retains exactly its original parameter. -/
theorem conicIncidenceFirstParameterHom_z :
    conicIncidenceFirstParameterHom a c ha hc (conicParameterZ c) =
      conicIncidenceFirstParameter a c hc := by
  change conicFirstToIncidence a c hc (conicParameterToFirst a c ha _) = _
  rw [conicParameterToFirst_z]
  rfl

/-- The second restriction retains exactly its original parameter. -/
theorem conicIncidenceSecondParameterHom_z :
    conicIncidenceSecondParameterHom a c ha hc (conicParameterZ c) =
      conicIncidenceSecondParameter a c hc := by
  change conicSecondToIncidence a c hc (conicSecondParameterEquiv a c ha _) = _
  rw [conicSecondParameterEquiv_z]
  rfl

/-- The incidence boundary as an open of the entire first parameter neighborhood. -/
def conicIncidenceFirstParameterMap : Spec (.of B) ⟶ Spec (.of P) :=
  Spec.map (CommRingCat.ofHom (conicIncidenceFirstParameterHom a c ha hc).toRingHom)

/-- The incidence boundary as an open of the entire second parameter neighborhood. -/
def conicIncidenceSecondParameterMap : Spec (.of B) ⟶ Spec (.of P) :=
  Spec.map (CommRingCat.ofHom (conicIncidenceSecondParameterHom a c ha hc).toRingHom)

/-- The first parameter restriction agrees on every original conic function. -/
@[reassoc] theorem conicIncidenceFirstParameterMap_conic :
    conicIncidenceFirstParameterMap a c ha hc ≫
      (conicFirstParameterIso a c ha).inv ≫ conicFirstOpenImmersion a c =
        Spec.map (CommRingCat.ofHom (algebraMap C₀ B)) := by
  change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro q
  change conicFirstToIncidence a c hc
    ((conicFirstParameterEquiv a c ha)
      ((conicFirstParameterEquiv a c ha).symm (algebraMap C₀ _ q))) = _
  rw [AlgEquiv.apply_symm_apply, conicFirstToIncidence_base]
  rfl

/-- The second parameter restriction also agrees on every original conic function. -/
@[reassoc] theorem conicIncidenceSecondParameterMap_conic :
    conicIncidenceSecondParameterMap a c ha hc ≫
      (conicSecondParameterIso a c ha).inv ≫ conicSecondOpenImmersion a c =
        Spec.map (CommRingCat.ofHom (algebraMap C₀ B)) := by
  change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro q
  change conicSecondToIncidence a c hc
    ((conicSecondParameterEquiv a c ha)
      ((conicSecondParameterEquiv a c ha).symm (algebraMap C₀ _ q))) = _
  rw [AlgEquiv.apply_symm_apply, conicSecondToIncidence_base]
  rfl

instance conicIncidenceFirstParameterMap_open :
    IsOpenImmersion (conicIncidenceFirstParameterMap a c ha hc) := by
  have : IsOpenImmersion (conicIncidenceFirstParameterMap a c ha hc ≫
      (conicFirstParameterIso a c ha).inv ≫ conicFirstOpenImmersion a c) := by
    rw [conicIncidenceFirstParameterMap_conic]
    exact IsOpenImmersion.of_isLocalization (conicT a c)
  exact IsOpenImmersion.of_comp _
    ((conicFirstParameterIso a c ha).inv ≫ conicFirstOpenImmersion a c)

instance conicIncidenceSecondParameterMap_open :
    IsOpenImmersion (conicIncidenceSecondParameterMap a c ha hc) := by
  have : IsOpenImmersion (conicIncidenceSecondParameterMap a c ha hc ≫
      (conicSecondParameterIso a c ha).inv ≫ conicSecondOpenImmersion a c) := by
    rw [conicIncidenceSecondParameterMap_conic]
    exact IsOpenImmersion.of_isLocalization (conicT a c)
  exact IsOpenImmersion.of_comp _
    ((conicSecondParameterIso a c ha).inv ≫ conicSecondOpenImmersion a c)

end FLT.Mazur.WeierstrassModificationX
