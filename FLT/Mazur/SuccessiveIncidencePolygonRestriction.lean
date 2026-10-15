/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.SuccessiveIncidenceCoefficientMap
public import FLT.Mazur.SuccessiveIncidencePolygonChart
public import FLT.Mazur.PolygonSmoothingCoefficientBranches

/-!
# The incidence comparison commutes with the original polygon coefficient map

The two presentations retain the same branch coordinates under restriction.
The polygon map here is the original tensor coefficient map.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.SuccessiveIncidence
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (π : R)
local notation "f" => algebraMap R S

/-- The incidence restriction retains its original scalar structure. -/
def coefficientAlgHom : Coordinate π →ₐ[R] Coordinate (f π) where
  __ := coefficientRingMap f π
  commutes' r := by
    change coefficientRingMap f π (algebraMap R _ r) = algebraMap R _ r
    rw [coefficientRingMap_algebraMap]
    exact (IsScalarTower.algebraMap_apply R S (Coordinate (f π)) r).symm

/-- The two presentations commute with the original polygon coefficient homomorphism. -/
theorem toPolygon_coefficientAlgHom :
    (PolygonSmoothing.coefficientAlgHom R S π).comp (toPolygon π) =
      ((toPolygon (f π)).restrictScalars R).comp (coefficientAlgHom R S π) := by
  apply hom_ext
  · change PolygonSmoothing.coefficientAlgHom R S π (toPolygon π (t π)) =
      toPolygon (f π) (coefficientRingMap f π (t π))
    rw [toPolygon_t, PolygonSmoothing.coefficientAlgHom_left,
      coefficientRingMap_t, toPolygon_t]
  · change PolygonSmoothing.coefficientAlgHom R S π (toPolygon π (u π)) =
      toPolygon (f π) (coefficientRingMap f π (u π))
    rw [toPolygon_u, PolygonSmoothing.coefficientAlgHom_right,
      coefficientRingMap_u, toPolygon_u]

/-- The actual tensor coefficient map is compatible with the incidence comparison. -/
theorem toPolygon_coefficientMap :
    (PolygonSmoothing.coefficientMap R S π).comp (toPolygon π).toRingHom =
      (toPolygon (f π)).toRingHom.comp (coefficientRingMap f π) :=
  congrArg AlgHom.toRingHom (toPolygon_coefficientAlgHom R S π)

/-- The original polygon coefficient projection commutes with the incidence isomorphism. -/
@[reassoc] theorem toPolygon_restriction_square :
    PolygonSmoothing.chartCoefficient R S π ≫
      Spec.map (CommRingCat.ofHom (toPolygon π).toRingHom) =
    Spec.map (CommRingCat.ofHom (toPolygon (f π)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (coefficientRingMap f π)) := by
  simp only [PolygonSmoothing.chartCoefficient, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun g => Spec.map (CommRingCat.ofHom g)) (toPolygon_coefficientMap R S π)

end FLT.Mazur.SuccessiveIncidence
