/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXConicGeometry
public import FLT.Mazur.WeierstrassModificationXConicIncidenceOrientation

/-!
# The ordered conic parameter origins

The origins of the two actual parameter opens are precisely the original
ordered conic markings, as algebra maps and as scheme morphisms.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (a c : R) (ha : IsUnit a)
local notation "C" => ConicCoordinate a c
local notation "O₁" => ConicFirstOpen a c
local notation "O₂" => ConicSecondOpen a c

/-- The first inverse parameter chart sends its origin to the first conic marking. -/
theorem conicFirstIncidencePoint_parameter :
    conicFirstIncidencePoint a c ha = (conicParameterOrigin c).comp
      ((conicFirstParameterEquiv a c ha).symm.toAlgHom.comp (Algebra.algHom R C O₁)) := by
  apply AlgHom.ext
  intro q
  exact conicFirstIncidenceEquiv_mk a c ha (algebraMap C O₁ q)

/-- The second inverse parameter chart sends its origin to the opposite conic marking. -/
theorem conicSecondIncidencePoint_parameter :
    conicSecondIncidencePoint a c ha = (conicParameterOrigin c).comp
      ((conicSecondParameterEquiv a c ha).symm.toAlgHom.comp (Algebra.algHom R C O₂)) := by
  apply AlgHom.ext
  intro q
  exact conicSecondIncidenceEquiv_mk a c ha (algebraMap C O₂ q)

/-- The first actual parameter origin factors the first ordered conic section. -/
@[reassoc] theorem conicFirstParameterIso_origin :
    Spec.map (CommRingCat.ofHom (conicParameterOrigin c).toRingHom) ≫
      (conicFirstParameterIso a c ha).inv ≫ conicFirstOpenImmersion a c =
        Spec.map (CommRingCat.ofHom (conicFirstIncidencePoint a c ha).toRingHom) := by
  rw [conicFirstIncidencePoint_parameter]
  change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

/-- The second actual parameter origin factors the opposite ordered conic section. -/
@[reassoc] theorem conicSecondParameterIso_origin :
    Spec.map (CommRingCat.ofHom (conicParameterOrigin c).toRingHom) ≫
      (conicSecondParameterIso a c ha).inv ≫ conicSecondOpenImmersion a c =
        Spec.map (CommRingCat.ofHom (conicSecondIncidencePoint a c ha).toRingHom) := by
  rw [conicSecondIncidencePoint_parameter]
  change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

end FLT.Mazur.WeierstrassModificationX
