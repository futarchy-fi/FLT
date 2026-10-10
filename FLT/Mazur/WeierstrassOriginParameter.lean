/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassInfinityCoordinateRegular
public import FLT.Mazur.WeierstrassIntegralZeroSection
public import FLT.Mazur.WeierstrassFlatSectionRegular

/-!
# A principal parameter on an actual neighborhood of the origin

The infinity equation reads zD = x^3, with D equal to one at the zero section.
After inverting D, the original x coordinate is regular and z has the same
principal ideal as x cubed. These identities hold over arbitrary base rings.
-/

@[expose] public noncomputable section

open Polynomial WeierstrassCurve

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The coefficient of z when the original infinity equation is written zD = x^3. -/
def originDenominator : Coordinate W 1 :=
  1 + algebraMap R _ W.a₁ * coord W 1 0 + algebraMap R _ W.a₃ * coord W 1 2 -
    algebraMap R _ W.a₂ * coord W 1 0 ^ 2 -
    algebraMap R _ W.a₄ * coord W 1 0 * coord W 1 2 -
    algebraMap R _ W.a₆ * coord W 1 2 ^ 2

/-- The exact original cubic equation near infinity. -/
theorem originDenominator_relation :
    coord W 1 2 * originDenominator W = coord W 1 0 ^ 3 := by
  have h := coord_equation W 1
  rw [Projective.equation_iff] at h
  simp only [coord_self, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆] at h
  unfold originDenominator
  linear_combination h

/-- The denominator equals one on the actual original zero section. -/
@[simp] theorem originDenominator_at_zero :
    chartInfinityEvaluation (S := R) W (originDenominator W) = 1 := by
  simp [originDenominator]

/-- The actual principal neighborhood containing the origin. -/
abbrev OriginNeighborhood := Localization.Away (originDenominator W)

/-- Original infinity coordinates restricted to the principal neighborhood. -/
def originCoordinate (i : Fin 3) : OriginNeighborhood W :=
  algebraMap (Coordinate W 1) (OriginNeighborhood W) (coord W 1 i)

/-- The denominator becomes a unit on the selected principal neighborhood. -/
theorem originDenominator_isUnit :
    IsUnit (algebraMap (Coordinate W 1) (OriginNeighborhood W) (originDenominator W)) :=
  IsLocalization.Away.algebraMap_isUnit _

/-- The original cubic identity survives restriction, without cancellation of nilpotents. -/
theorem originCoordinate_relation :
    originCoordinate W 2 *
      algebraMap (Coordinate W 1) (OriginNeighborhood W) (originDenominator W) =
        originCoordinate W 0 ^ 3 := by
  simpa only [originCoordinate, map_mul, map_pow] using
    congrArg (algebraMap (Coordinate W 1) (OriginNeighborhood W)) (originDenominator_relation W)

/-- The original z coordinate remains regular on this principal neighborhood. -/
theorem originCoordinate_z_regular : IsRegular (originCoordinate W 2) :=
  flatRingHom_isRegular (algebraMap (Coordinate W 1) (OriginNeighborhood W))
    (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _
      (Submonoid.powers (originDenominator W)))) (infinityChart_coord_z_regular W)

/-- The original x coordinate is a regular parameter on the selected neighborhood. -/
theorem originCoordinate_x_regular : IsRegular (originCoordinate W 0) := by
  have hp : IsRegular (originCoordinate W 0 ^ 3) := by
    rw [← originCoordinate_relation]
    exact (originCoordinate_z_regular W).mul (originDenominator_isUnit W).isRegular
  have hl : IsLeftRegular (originCoordinate W 0) := by
    intro a b h
    apply hp.left
    linear_combination originCoordinate W 0 ^ 2 * h
  exact ⟨hl, fun a b h ↦ hl (by simpa only [mul_comm] using h)⟩

/-- The actual z coordinate generates the cube of the parameter's principal ideal. -/
theorem originCoordinate_span_z :
    Ideal.span {originCoordinate W 2} = Ideal.span {originCoordinate W 0 ^ 3} := by
  rw [← originCoordinate_relation]
  exact (Ideal.span_singleton_mul_right_unit (originDenominator_isUnit W) _).symm

end FLT.Mazur.WeierstrassIntegralChart
