/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXShearContraction
public import FLT.Mazur.WeierstrassSuccessiveXHorizontalLocalization

/-!
# The retained horizontal principal open under successive shear

The original u-coordinate is fixed. Localization therefore compares the
entire preceding-side boundary, including all its regular functions.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 r : R)
local notation "U" => rootShearCurve W r
local notation "A" => HorizontalOpen W s π b3 b4 b6
local notation "B" => HorizontalOpen U s π b3 (b4 - r * b3) b6

/-- Localizing at the retained original horizontal coordinate preserves shear. -/
def horizontalShearEquiv : A ≃ₐ[R] B :=
  IsLocalization.algEquivOfAlgEquiv A B
    (M := Submonoid.powers (coord W s π b3 b4 b6 2))
    (T := Submonoid.powers (coord U s π b3 (b4 - r * b3) b6 2))
    (shearEquiv W s π b3 b4 b6 r) (by
      rw [Submonoid.map_powers]
      congr 1
      exact shearForward_coord W s π b3 b4 b6 r 2)

/-- The localized retained-boundary comparison keeps every original incidence function. -/
theorem horizontalShearEquiv_base (z : Coordinate W s π b3 b4 b6) :
    horizontalShearEquiv W s π b3 b4 b6 r (algebraMap _ A z) =
      algebraMap _ B (shearForward W s π b3 b4 b6 r z) := by
  rw [horizontalShearEquiv, IsLocalization.algEquivOfAlgEquiv_eq]
  rfl

end FLT.Mazur.WeierstrassSuccessiveX
