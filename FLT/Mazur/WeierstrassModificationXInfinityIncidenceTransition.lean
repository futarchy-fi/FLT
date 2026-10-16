/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXInitialInfinityTransition
public import FLT.Mazur.WeierstrassInfinityNilpotentIncidence

/-!
# The regular infinity incidence follows the original projective transition

On the entire original D(y), the constructed regular infinity coordinate is
exactly the original t=s/x. This compares the actual projective map, retaining
all divided coefficients and the original localization.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassModificationX
open WeierstrassIntegralChart
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
local notation "A" => Coordinate W s b3 b4 b6
local notation "Y" => Localization.Away (y W s b3 b4 b6)
local notation "g" => algebraMap A Y
local notation "F" => initialInfinityTransition W s b3 b4 b6 h3 h4 h6
local notation "u" => coord W 1 0
local notation "w" => coord W 1 2

/-- The original projective Z/Y restricts to precisely the inverse original y. -/
theorem initialInfinityTransition_z : F w = IsLocalization.Away.invSelf (y W s b3 b4 b6) := by
  change initialInfinityOverlapMap W s b3 b4 b6 h3 h4 h6
    (transitionBase W 2 1 (coord W 1 2)) = _
  rw [transitionBase_coord, map_mul, overlapCoord, coord_self]
  simp only [map_one, mul_one]
  exact initialInfinityOverlapMap_inverse W s b3 b4 b6 h3 h4 h6

/-- The original X/Y is inverse to the original slope on the complete y-boundary. -/
theorem initialInfinityTransition_x_mul_v : F u * g (v W s b3 b4 b6) = 1 := by
  rw [initialInfinityTransition_x]
  calc
    _ = g (y W s b3 b4 b6) * IsLocalization.Away.invSelf (y W s b3 b4 b6) := by
      rw [y, map_mul]
      ring
    _ = 1 := IsLocalization.Away.mul_invSelf _

/-- The original X/Y coordinate is a unit on exactly this full original boundary. -/
theorem initialInfinityTransition_x_isUnit : IsUnit (F u) :=
  isUnit_iff_exists_inv.mpr ⟨g (v W s b3 b4 b6),
    initialInfinityTransition_x_mul_v W s b3 b4 b6 h3 h4 h6⟩

variable (I : Ideal R) (hI : IsNilpotent I)
  (h2I : W.a₂ ∈ I) (h3I : W.a₃ ∈ I) (h4I : W.a₄ ∈ I) (h6I : W.a₆ ∈ I)
local notation "t∞" => nilpotentInfinityIncidence W I hI h2I h3I h4I h6I s

/-- The constructed regular extension pulls back to the unchanged original incidence coordinate. -/
theorem initialInfinityTransition_incidence : F t∞ = g (t W s b3 b4 b6) := by
  apply (initialInfinityTransition_x_isUnit W s b3 b4 b6 h3 h4 h6).mul_right_cancel
  have ht := congrArg F (nilpotentInfinityIncidence_mul W I hI h2I h3I h4I h6I s)
  rw [map_mul, map_mul, AlgHom.commutes, initialInfinityTransition_z] at ht
  rw [ht, initialInfinityTransition_x]
  have hi := congrArg g (incidence W s b3 b4 b6)
  rw [map_mul, ← IsScalarTower.algebraMap_apply R A Y] at hi
  calc
    _ = (g (t W s b3 b4 b6) * g (x W s b3 b4 b6)) *
        IsLocalization.Away.invSelf (y W s b3 b4 b6) := by rw [hi]
    _ = _ := by ring

end FLT.Mazur.WeierstrassModificationX
