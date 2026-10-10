/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassOriginPoleCoordinates

/-!
# Pole bounds in the actual parameter neighborhood

A bound means that multiplying the original affine function by a power of the
original parameter extends to the actual origin neighborhood. The extension
is unique, and bounds respect addition, multiplication, and increasing order.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The punctured restriction of the actual origin ring is injective. -/
theorem originPunctureRestriction_injective :
    Function.Injective (algebraMap (OriginNeighborhood W) (OriginPuncture W)) := by
  apply IsLocalization.injective (OriginPuncture W) (M := Submonoid.powers (originCoordinate W 0))
  rintro _ ⟨n, rfl⟩
  exact ((originCoordinate_x_regular W).pow n).mem_nonZeroDivisors

/-- The actual punctured parameter is the image of the original local parameter. -/
theorem originPuncture_parameter :
    algebraMap (OriginNeighborhood W) (OriginPuncture W) (originCoordinate W 0) =
      originPunctureChart W (coord W 1 0) := by
  change algebraMap (OriginNeighborhood W) (OriginPuncture W)
    (algebraMap (Coordinate W 1) (OriginNeighborhood W) (coord W 1 0)) = _
  rw [← IsScalarTower.algebraMap_apply]
  rfl

/-- A pole bound requires an actual regular numerator on the original origin neighborhood. -/
def HasOriginPoleBound (a : Coordinate W 2) (n : ℕ) : Prop :=
  ∃ b : OriginNeighborhood W, algebraMap (OriginNeighborhood W) (OriginPuncture W) b =
    originPunctureAffine W a * originPunctureChart W (coord W 1 0) ^ n

/-- The actual regular numerator is unique, including over nonreduced bases. -/
theorem originPole_numerator_unique (a : Coordinate W 2) (n : ℕ)
    (b c : OriginNeighborhood W)
    (hb : algebraMap (OriginNeighborhood W) (OriginPuncture W) b =
      originPunctureAffine W a * originPunctureChart W (coord W 1 0) ^ n)
    (hc : algebraMap (OriginNeighborhood W) (OriginPuncture W) c =
      originPunctureAffine W a * originPunctureChart W (coord W 1 0) ^ n) : b = c :=
  originPunctureRestriction_injective W (hb.trans hc.symm)

/-- Increasing the allowed pole order multiplies the actual numerator by a parameter power. -/
theorem originPole_mono (a : Coordinate W 2) {n m : ℕ} (hnm : n ≤ m)
    (h : HasOriginPoleBound W a n) : HasOriginPoleBound W a m := by
  obtain ⟨b, hb⟩ := h
  refine ⟨b * originCoordinate W 0 ^ (m - n), ?_⟩
  rw [map_mul, map_pow, originPuncture_parameter, hb, mul_assoc, ← pow_add,
    Nat.add_sub_of_le hnm]

/-- Adding functions with the same bound adds their actual regular numerators. -/
theorem originPole_add (a b : Coordinate W 2) (n : ℕ)
    (ha : HasOriginPoleBound W a n) (hb : HasOriginPoleBound W b n) :
    HasOriginPoleBound W (a + b) n := by
  obtain ⟨c, hc⟩ := ha
  obtain ⟨d, hd⟩ := hb
  refine ⟨c + d, ?_⟩
  rw [map_add, hc, hd, map_add, add_mul]

/-- Multiplying actual functions adds their pole bounds. -/
theorem originPole_mul (a b : Coordinate W 2) (n m : ℕ)
    (ha : HasOriginPoleBound W a n) (hb : HasOriginPoleBound W b m) :
    HasOriginPoleBound W (a * b) (n + m) := by
  obtain ⟨c, hc⟩ := ha
  obtain ⟨d, hd⟩ := hb
  refine ⟨c * d, ?_⟩
  rw [map_mul, hc, hd, map_mul, pow_add]
  ring

/-- Original base coefficients have pole bound zero. -/
theorem originPole_constant (r : R) : HasOriginPoleBound W (algebraMap R _ r) 0 := by
  refine ⟨algebraMap R _ r, ?_⟩
  rw [AlgHom.commutes, pow_zero, mul_one, ← IsScalarTower.algebraMap_apply]

/-- The actual original affine x coordinate has pole bound two. -/
theorem originPole_x : HasOriginPoleBound W (coord W 2 0) 2 := by
  refine ⟨algebraMap (Coordinate W 1) (OriginNeighborhood W) (originDenominator W), ?_⟩
  rw [← IsScalarTower.algebraMap_apply, originPunctureAffine_x_pole]
  rfl

/-- The actual original affine y coordinate has pole bound three. -/
theorem originPole_y : HasOriginPoleBound W (coord W 2 1) 3 := by
  refine ⟨algebraMap (Coordinate W 1) (OriginNeighborhood W) (originDenominator W), ?_⟩
  rw [← IsScalarTower.algebraMap_apply, originPunctureAffine_y_pole]
  rfl

end FLT.Mazur.WeierstrassIntegralChart
