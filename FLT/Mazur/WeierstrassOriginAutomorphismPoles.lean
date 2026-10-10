/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassOriginAutomorphismSections
public import FLT.Mazur.WeierstrassLowPoleCoordinates

/-!
# Original automorphisms preserve pole bounds and have triangular coordinates

Transporting the actual global divisor section proves pole preservation
without requiring the parameter neighborhood to be invariant. The exact
low-pole spaces then give the two triangular coordinate formulas.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

variable {R : Type} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)
  (e : integralCurve W ≅ integralCurve W)
  (hb : e.hom ≫ integralCurveStructure W = integralCurveStructure W)
  (hz : integralCurveZero W ≫ e.hom = integralCurveZero W)

/-- Every actual origin-preserving automorphism preserves the explicit original pole bounds. -/
theorem originAutCoordinateHom_pole (n : ℕ) (a : Coordinate W 2)
    (ha : HasOriginPoleBound W a n) :
    HasOriginPoleBound W (originAutCoordinateHom W hΔ e hb hz a) n := by
  obtain ⟨s, hs⟩ := originPole_exists_global_section W n a ha
  exact originPole_of_global_section W n _ (originAutDivisorTransport W e hz n s)
    (originAutDivisorTransport_affine W e hz hΔ hb n a s hs)

/-- The actual x-coordinate pullback is a linear combination of the original 1 and x. -/
theorem originAutCoordinateHom_x_triangular : ∃ r s : R,
    originAutCoordinateHom W hΔ e hb hz (coord W 2 0) =
      algebraMap R _ r + algebraMap R _ s * coord W 2 0 :=
  (originPole_two_iff W _).mp
    (originAutCoordinateHom_pole W hΔ e hb hz 2 _ (originPole_x W))

/-- The actual y-coordinate pullback lies in the original span of 1, x, and y. -/
theorem originAutCoordinateHom_y_triangular : ∃ r s t : R,
    originAutCoordinateHom W hΔ e hb hz (coord W 2 1) =
      algebraMap R _ r + algebraMap R _ s * coord W 2 0 +
        algebraMap R _ t * coord W 2 1 :=
  (originPole_three_iff W _).mp
    (originAutCoordinateHom_pole W hΔ e hb hz 3 _ (originPole_y W))

end FLT.Mazur.WeierstrassIntegralChart
