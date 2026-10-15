/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.SuccessiveIncidencePolygonRestriction

/-!
# Full incidence Laurent evaluations commute with coefficient restriction

The original positive Laurent parameter and its reciprocal are retained.
The equality applies to every incidence function, including constructed slopes.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.SuccessiveIncidence
universe u
variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (π : R)

/-- The complete incidence Laurent evaluation commutes with any coefficient map. -/
theorem leftLaurent_coefficientRingMap (z : Coordinate π) :
    PolygonScalingNaturality.coeffMap f
      (PolygonSmoothing.leftLaurentMap π (toPolygon π z)) =
    PolygonSmoothing.leftLaurentMap (f π)
      (toPolygon (f π) (coefficientRingMap f π z)) := by
  let _ := f.toAlgebra
  have hp := DFunLike.congr_fun (toPolygon_coefficientAlgHom R S π) z
  have hl := DFunLike.congr_fun (PolygonSmoothing.leftLaurent_coefficient R S π)
    (toPolygon π z)
  change PolygonSmoothing.coefficientAlgHom R S π (toPolygon π z) =
    toPolygon (f π) (coefficientRingMap f π z) at hp
  change PolygonSmoothing.leftLaurentMap (f π)
    (PolygonSmoothing.coefficientAlgHom R S π (toPolygon π z)) =
      PolygonScalingNaturality.coeffMap f
        (PolygonSmoothing.leftLaurentMap π (toPolygon π z)) at hl
  exact hl.symm.trans (congrArg (PolygonSmoothing.leftLaurentMap (f π)) hp)

end FLT.Mazur.SuccessiveIncidence
