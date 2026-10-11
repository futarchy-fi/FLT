/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitDepthExceptionalScaling
public import FLT.Mazur.RegularCenterQuotientLinear

/-!
# Horizontal scaling on the two original exceptional branches

The actual branch characters force reciprocal horizontal scalings. The
first conic branch has Y/X = 0; the second has Y/X = -a₁. The tangent
coefficient remains a unit over every residue coefficient ring.
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

local notation "Q" => quotient I φ z hI

include D hk hz hψ hJ hx hy hq in
/-- The zero-slope branch is preserved and its horizontal quotient has inverse character. -/
theorem splitDepthExceptional_first_horizontal
    (h0 : ψ (Q y (H).1.2) = 0) :
    ψ (Q Y (H).2.2) = 0 ∧
      ψ (Q X (H).2.1) = (↑(r * q⁻¹) : C) * ψ (Q x (H).1.1) := by
  have hfirst := splitDepthExceptional_first_scaling D d hk b f φ z hI hz ψ hψ hJ
    r q hx hy hq
  have hsecond := splitDepthExceptional_second_scaling D d hk b f φ z hI hz ψ hψ hJ
    r q hx hy hq
  rw [h0, mul_zero] at hfirst
  refine ⟨hfirst, ?_⟩
  rw [quotient_add_mul I φ z hI hz X Y a (H).2.1 (H).2.2,
    quotient_add_mul I φ z hI hz x y a (H).1.1 (H).1.2,
    map_add, map_mul, map_add, map_mul, hfirst, h0, zero_add, zero_add] at hsecond
  apply ((D.a₁_unit.map (algebraMap R S)).map φ |>.map ψ).mul_left_inj.mp
  linear_combination hsecond

include D hk hz hψ hJ hx hy hq in
/-- The opposite branch is preserved and its horizontal quotient has the direct character. -/
theorem splitDepthExceptional_second_horizontal
    (h0 : ψ (Q (y + a * x) ((I).add_mem (H).1.2 ((I).mul_mem_left a (H).1.1))) = 0) :
    ψ (Q (Y + a * X) ((I).add_mem (H).2.2 ((I).mul_mem_left a (H).2.1))) = 0 ∧
      ψ (Q X (H).2.1) = (↑(q * r⁻¹) : C) * ψ (Q x (H).1.1) := by
  have hfirst := splitDepthExceptional_first_scaling D d hk b f φ z hI hz ψ hψ hJ
    r q hx hy hq
  have hsecond := splitDepthExceptional_second_scaling D d hk b f φ z hI hz ψ hψ hJ
    r q hx hy hq
  rw [h0, mul_zero] at hsecond
  refine ⟨hsecond, ?_⟩
  rw [quotient_add_mul I φ z hI hz x y a (H).1.1 (H).1.2, map_add, map_mul] at h0
  rw [quotient_add_mul I φ z hI hz X Y a (H).2.1 (H).2.2, map_add, map_mul] at hsecond
  apply ((D.a₁_unit.map (algebraMap R S)).map φ |>.map ψ).mul_left_inj.mp
  linear_combination hsecond - hfirst - (↑(q * r⁻¹) : C) * h0

end FLT.Mazur.WeierstrassIntegralChart
