/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassProductOverlap

/-!
# Integral output transitions for unit-scaled coordinate maps

Two normalized coordinate maps related by a common unit factor determine a
map to the actual chart overlap. Both output maps are its restrictions.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (j k : Fin 3)
  (a : Coordinate W j →ₐ[R] S) (b : Coordinate W k →ₐ[R] S)
  (q : S) (hq : IsUnit q)
  (h : ∀ i, b (coord W k i) = q * a (coord W j i))

include h in
/-- The first normalizing coordinate of the second map is exactly the common factor. -/
theorem scaledChart_normalizing : b (coord W k j) = q := by
  simpa only [coord_self, map_one, mul_one] using h j

include hq h in
/-- The second output map lands in the integral overlap of the two target charts. -/
theorem scaledChart_isUnit : IsUnit (b (coord W k j)) := by
  rw [scaledChart_normalizing W j k a b q h]
  exact hq

/-- The actual output-overlap lift determined by the second map. -/
def scaledChartLift : Overlap W k j →ₐ[R] S :=
  overlapLift W k j b (scaledChart_isUnit W j k a b q hq h)

/-- The lift restricts to the second output map. -/
theorem scaledChartLift_restriction :
    (scaledChartLift W j k a b q hq h).comp (overlapRestriction W k j) = b :=
  overlapLift_restriction W k j b _

/-- The lift retains the normalized coordinates of the second output. -/
@[simp] theorem scaledChartLift_coord (i : Fin 3) :
    scaledChartLift W j k a b q hq h (overlapCoord W k j i) = b (coord W k i) :=
  DFunLike.congr_fun (scaledChartLift_restriction W j k a b q hq h) (coord W k i)

/-- The normalizing inverse on the overlap cancels the common output factor. -/
theorem scaledChartLift_inverse :
    scaledChartLift W j k a b q hq h (overlapInverse W k j) * q = 1 := by
  have hi := congrArg (scaledChartLift W j k a b q hq h) (overlapInverse_mul W k j)
  simpa only [map_mul, map_one, scaledChartLift_coord,
    scaledChart_normalizing W j k a b q h] using hi

/-- Changing output charts recovers exactly the first normalized map. -/
theorem scaledChartLift_transition :
    (scaledChartLift W j k a b q hq h).comp (transitionBase W k j) = a := by
  apply hom_ext
  intro i
  change scaledChartLift W j k a b q hq h (transitionBase W k j (coord W j i)) = _
  rw [transitionBase_coord, map_mul, scaledChartLift_coord, h,
    ← mul_assoc, scaledChartLift_inverse, one_mul]

end FLT.Mazur.WeierstrassIntegralChart
