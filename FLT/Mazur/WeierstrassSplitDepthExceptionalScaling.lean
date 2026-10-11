/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitDepthExceptionalCharacters
public import FLT.Mazur.WeierstrassOrdinaryCenterResidueSlope

/-!
# Reciprocal unit scalings on actual exceptional quotients

The actual integral slope restricts to the smooth parameter unit. Combining
this with the depth-derived conormal relations gives explicit inverse scalings.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassIntegralChart
open IsLocalRing WeierstrassDividedDepth RegularCenter
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S B C : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  [CommRing S] [Algebra R S] [CommRing B] [CommRing C]
  {W : WeierstrassCurve R} {π : R} {depth k : ℕ}
  (D : SplitNodeDepth W π depth) (d : Data W π k) (hk : 2 * k ≤ depth)
  (b : Bool) (f : additionChartRing W (ordinaryIndex b) →ₐ[R] S)
local notation "I" => Ideal.map
  (AlgHom.toRingHom (AlgHom.comp f (ordinaryInputRight W b)))
  (modificationChartCenter W (π ^ k) 2)
local notation "J" => Ideal.map (algebraMap R S) (maximalIdeal R)
local notation "a" => algebraMap R S W.a₁
local notation "x" => f (ordinaryInputRight W b (coord W 2 0))
local notation "y" => f (ordinaryInputRight W b (coord W 2 1))
local notation "X" => f (ordinaryChartAddition W b (coord W 2 0))
local notation "Y" => f (ordinaryChartAddition W b (coord W 2 1))
local notation "l" => f (ordinaryChartSlope W b)

local notation "H" => splitDepthExceptional_coordinates_mem d b f
variable (φ : S →+* B) (z : B) (hI : ((modificationChartCenter W (π ^ k) 2).map
    (f.comp (ordinaryInputRight W b)).toRingHom).map φ = Ideal.span {z}) (hz : IsRegular z)
  (ψ : B →+* C) (hψ : ψ z = 0) (hJ : (maximalIdeal R).map (algebraMap R S) ≤ RingHom.ker (ψ.comp φ))
  (r q : Cˣ)
  (hx : ψ (φ (f (ordinaryInputLeft W b (coord W 2 0)))) = (r : C) * q)
  (hy : ψ (φ (f (ordinaryInputLeft W b (coord W 2 1)))) = (r : C) ^ 2 * q)
  (hq : (q : C) = (r : C) + ψ (φ (algebraMap R S W.a₁)))

include D hk hz hψ hJ hx hy hq in
/-- The original first branch quotient scales by the actual parameter ratio. -/
theorem splitDepthExceptional_first_scaling :
    ψ (quotient I φ z hI Y (H).2.2) =
      (↑(q * r⁻¹) : C) * ψ (quotient I φ z hI y (H).1.2) := by
  have h := splitDepthExceptional_first_character D d hk b f φ z hI hz ψ hψ hJ
  have hl := ordinaryCenterResidue_slope W (π ^ k) b f φ z hI ψ hψ r q hx hy
  have hl' := ordinaryCenterResidue_opposite_slope
    W (π ^ k) b f φ z hI ψ hψ r q hx hy hq
  change ψ (φ l) = (r : C) at hl
  change ψ (φ (l + a)) = (q : C) at hl'
  rw [hl, hl'] at h
  simp only [Units.val_mul]
  linear_combination (↑r⁻¹ : C) * h -
    ψ (quotient I φ z hI Y (H).2.2) * (Units.mul_inv r)

include D hk hz hψ hJ hx hy hq in
/-- The other original branch quotient scales by the reciprocal parameter ratio. -/
theorem splitDepthExceptional_second_scaling :
    ψ (quotient I φ z hI (Y + a * X)
      ((I).add_mem (H).2.2 ((I).mul_mem_left a (H).2.1))) =
    (↑(r * q⁻¹) : C) * ψ (quotient I φ z hI (y + a * x)
      ((I).add_mem (H).1.2 ((I).mul_mem_left a (H).1.1))) := by
  have h := splitDepthExceptional_second_character D d hk b f φ z hI hz ψ hψ hJ
  have hl := ordinaryCenterResidue_slope W (π ^ k) b f φ z hI ψ hψ r q hx hy
  have hl' := ordinaryCenterResidue_opposite_slope
    W (π ^ k) b f φ z hI ψ hψ r q hx hy hq
  change ψ (φ l) = (r : C) at hl
  change ψ (φ (l + a)) = (q : C) at hl'
  rw [hl, hl'] at h
  simp only [Units.val_mul]
  linear_combination (↑q⁻¹ : C) * h -
    ψ (quotient I φ z hI (Y + a * X)
      ((I).add_mem (H).2.2 ((I).mul_mem_left a (H).2.1))) * (Units.mul_inv q)

end FLT.Mazur.WeierstrassIntegralChart
