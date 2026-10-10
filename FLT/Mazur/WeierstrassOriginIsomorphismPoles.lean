/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassOriginIsomorphismSections
public import FLT.Mazur.WeierstrassLowPoleCoordinates

/-!
# Triangular coordinates of arbitrary origin-preserving isomorphisms

The actual divisor-section transport preserves pole bounds between distinct
cubics. The exact low-pole spaces then force both triangular coordinate forms.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

variable {R : Type} [CommRing R] (W V : WeierstrassCurve R) (hV : IsUnit V.Δ)
  (e : integralCurve W ≅ integralCurve V)
  (hb : e.hom ≫ integralCurveStructure V = integralCurveStructure W)
  (hz : integralCurveZero W ≫ e.hom = integralCurveZero V)

/-- Pullback by the actual isomorphism preserves every explicit origin pole bound. -/
theorem originIsoCoordinateHom_pole (n : ℕ) (a : Coordinate V 2)
    (ha : HasOriginPoleBound V a n) :
    HasOriginPoleBound W (originIsoCoordinateHom W V hV e hb hz a) n := by
  obtain ⟨s, hs⟩ := originPole_exists_global_section V n a ha
  exact originPole_of_global_section W n _ (originIsoDivisorTransport W V e hz n s)
    (originIsoDivisorTransport_affine W V e hz hV hb n a s hs)

/-- The target abscissa pulls back to the source span of 1 and x. -/
theorem originIsoCoordinateHom_x_triangular : ∃ r s : R,
    originIsoCoordinateHom W V hV e hb hz (coord V 2 0) =
      algebraMap R _ r + algebraMap R _ s * coord W 2 0 :=
  (originPole_two_iff W _).mp
    (originIsoCoordinateHom_pole W V hV e hb hz 2 _ (originPole_x V))

/-- The target ordinate pulls back to the source span of 1, x, and y. -/
theorem originIsoCoordinateHom_y_triangular : ∃ r s t : R,
    originIsoCoordinateHom W V hV e hb hz (coord V 2 1) =
      algebraMap R _ r + algebraMap R _ s * coord W 2 0 +
        algebraMap R _ t * coord W 2 1 :=
  (originPole_three_iff W _).mp
    (originIsoCoordinateHom_pole W V hV e hb hz 3 _ (originPole_y V))

end FLT.Mazur.WeierstrassIntegralChart
