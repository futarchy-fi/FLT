/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassOriginImageEquation
public import FLT.Mazur.ModuleSheafBinarySections

/-!
# Matching divisor sections on the original full overlap

The sheaf overlap condition is exactly the regular-numerator equation in
the original puncture ring. This compares actual sections, over any base ring.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.AffineImmersionSectionCoordinates
open FLT.Mazur.ModuleSheafBinarySections

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The section on the original affine chart is multiplication by the original function. -/
def originAffinePoleSection (n : ℕ) (a : Coordinate W 2) :
    Γ(originDivisorLine W n, (originAffineOpen W).1) :=
  (coordinates (integralCurveChart W 2)).symm a •
    FCurve.divisorSection (originIdealSheaf_power_effectiveCartier W n) (originAffineOpen W).1

/-- The original equation gives numerator coordinates on the full overlap. -/
def originOverlapNumerator (n : ℕ) :
    Γ(originDivisorLine W n, (originOverlapOpen W).1) ≃ₗ[Γ(integralCurve W,
      (originOverlapOpen W).1)] Γ(integralCurve W, (originOverlapOpen W).1) :=
  FCurve.divisorNumerator (originIdealSheaf_power_effectiveCartier W n)
    (originOverlapOpen W)
    ((integralCurve W).presheaf.map (homOfLE (originOverlapOpen_le_image W)).op
      (originImageParameter W ^ n))
    (FCurve.regular_restrict (originOverlapOpen_le_image W)
      ((originImageParameter_regular W).pow n))
    (FCurve.ideal_eq_span_restrict _ (originOverlapOpen_le_image W)
      (originImageIdeal_power_equation W n))

/-- A neighborhood section restricts with exactly its original regular numerator. -/
theorem originOverlapNumerator_image (n : ℕ)
    (s : Γ(originDivisorLine W n, (originImageOpen W).1)) :
    coordinates (originPunctureToCurve W)
      (originOverlapNumerator W n (res (originDivisorLine W n)
        (originOverlapOpen_le_image W) s)) =
      algebraMap (OriginNeighborhood W) (OriginPuncture W) (originImageNumeratorRing W n s) := by
  have hn : originOverlapNumerator W n
      (res (originDivisorLine W n) (originOverlapOpen_le_image W) s) =
      (integralCurve W).presheaf.map (homOfLE (originOverlapOpen_le_image W)).op
        (originImageNumerator W n s) :=
    FCurve.divisorNumerator_restrict (originIdealSheaf_power_effectiveCartier W n)
      (originImageOpen W) (originImageParameter W ^ n)
      ((originImageParameter_regular W).pow n) (originImageIdeal_power_equation W n)
      (originOverlapOpen_le_image W) s
  rw [hn, originImageCoordinates_restrict]
  rfl

/-- The affine multiplication section has the expected punctured numerator. -/
theorem originOverlapNumerator_affine (n : ℕ) (a : Coordinate W 2) :
    coordinates (originPunctureToCurve W)
      (originOverlapNumerator W n (res (originDivisorLine W n)
        (originOverlapOpen_le_affine W) (originAffinePoleSection W n a))) =
      originPunctureAffine W a * originPunctureChart W (coord W 1 0) ^ n := by
  dsimp only [originOverlapNumerator, originAffinePoleSection, originDivisorLine, res]
  rw [FCurve.divisorCanonical_smul_restrict, FCurve.divisorNumerator_canonical, map_mul,
    originImageParameter_restrict, originAffineCoordinates_restrict, RingEquiv.apply_symm_apply]

/-- Actual overlap compatibility is precisely the original pole-numerator equation. -/
theorem originPole_overlap_iff (n : ℕ) (a : Coordinate W 2)
    (s : Γ(originDivisorLine W n, (originImageOpen W).1)) :
    res (originDivisorLine W n) (originOverlapOpen_le_image W) s =
        res (originDivisorLine W n) (originOverlapOpen_le_affine W)
          (originAffinePoleSection W n a) ↔
      algebraMap (OriginNeighborhood W) (OriginPuncture W) (originImageNumeratorRing W n s) =
        originPunctureAffine W a * originPunctureChart W (coord W 1 0) ^ n := by
  rw [← (originOverlapNumerator W n).injective.eq_iff,
    ← (coordinates (originPunctureToCurve W)).injective.eq_iff,
    originOverlapNumerator_image, originOverlapNumerator_affine]

end FLT.Mazur.WeierstrassIntegralChart
