/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitDepthExceptionalBranches
public import FLT.Mazur.RegularCenterOriginalFractionRatios
public import FLT.Mazur.WeierstrassModificationReesProjCover

/-!
# Actual original conic coordinates under integral addition

Original horizontal fraction lifts of the input and output retain the
integral addition map. On the two initial conic branches their scale/X
coordinates transform by opposite characters and their Y/X slopes are fixed.
The input denominator need only be a unit after residue restriction.
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

open WeierstrassModificationReesCoordinates BlowupFractionChart
local notation "I₀" => modificationChartCenter W (π ^ k) 2
local notation "sx" => horizontalScale W (π ^ k)
local notation "yx" => horizontalVertical W (π ^ k)
variable (L M : chart (modificationChartCenter W (π ^ k) 2) (coord W 2 0) →+* B)
  (hL : ∀ t, L (algebraMap (Coordinate W 2) _ t) = φ (f (ordinaryInputRight W b t)))
  (hM : ∀ t, M (algebraMap (Coordinate W 2) _ t) = φ (f (ordinaryChartAddition W b t)))

omit [IsDomain R] [IsLocalRing R] in
include hz hL hM in
/-- Both original horizontal lifts have their actual scale and vertical quotient identities. -/
theorem splitDepthOriginalFraction_ratios :
    (Q x (H).1.1 * L sx = Q (algebraMap R S (π ^ k)) (splitDepthConormal_scale_mem b f) ∧
      Q X (H).2.1 * M sx = Q (algebraMap R S (π ^ k)) (splitDepthConormal_scale_mem b f)) ∧
    (Q x (H).1.1 * L yx = Q y (H).1.2 ∧ Q X (H).2.1 * M yx = Q Y (H).2.2) := by
  have hs := splitDepthConormal_scale_mem b f (π := π) (k := k)
  have hsc (g : Coordinate W 2 →ₐ[R] S) :
      g (algebraMap R (Coordinate W 2) (π ^ k)) = algebraMap R S (π ^ k) := g.commutes _
  have hin := originalLift_ratio_quotient I₀ I (f.comp (ordinaryInputRight W b)).toRingHom
    φ z hI hz (coord W 2 0) (H).1.1 L hL
  have hout := originalLift_ratio_quotient I₀ I (f.comp (ordinaryChartAddition W b)).toRingHom
    φ z hI hz (coord W 2 0) (H).2.1 M hM
  refine ⟨⟨?_, ?_⟩, ⟨hin _ (centerGenerators_mem W (π ^ k) 2) (H).1.2,
    hout _ (centerGenerators_mem W (π ^ k) 2) (H).2.2⟩⟩
  · simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, centerGenerators,
      Matrix.cons_val_zero, hsc, horizontalScale, AlgHom.comp_apply,
      modificationChartCenter_affine] using
      hin _ (centerGenerators_mem W (π ^ k) 0)
        (by simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, centerGenerators,
          Matrix.cons_val_zero, hsc] using hs)
  · simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, centerGenerators,
      Matrix.cons_val_zero, hsc, horizontalScale, AlgHom.comp_apply,
      modificationChartCenter_affine] using
      hout _ (centerGenerators_mem W (π ^ k) 0)
        (by simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, centerGenerators,
          Matrix.cons_val_zero, hsc] using hs)

variable (hu : IsUnit (ψ (quotient
    ((modificationChartCenter W (π ^ k) 2).map (f.comp (ordinaryInputRight W b)).toRingHom)
    φ z hI (f (ordinaryInputRight W b (coord W 2 0)))
    (splitDepthExceptional_coordinates_mem d b f).1.1)))

include D hk hz hψ hJ hx hy hq hL hM hu in
/-- On the first original conic branch, scale/X has the direct smooth character. -/
theorem splitDepthOriginalFraction_first (h0 : ψ (L yx) = 0) :
    ψ (M sx) = (↑(q * r⁻¹) : C) * ψ (L sx) ∧ ψ (M yx) = 0 := by
  obtain ⟨⟨hs, hS⟩, ⟨hv, hV⟩⟩ := splitDepthOriginalFraction_ratios d b f φ z hI hz L M hL hM
  have hs := congrArg ψ hs
  have hS := congrArg ψ hS
  have hv := congrArg ψ hv
  have hV := congrArg ψ hV
  simp only [map_mul] at hs hS hv hV
  have hzero : ψ (Q y (H).1.2) = 0 := by rw [← hv, h0, mul_zero]
  obtain ⟨hY, hX⟩ := splitDepthExceptional_first_horizontal
    D d hk b f φ z hI hz ψ hψ hJ r q hx hy hq hzero
  rw [hX] at hS hV
  have ht : (↑(q * r⁻¹) : C) * (↑(r * q⁻¹) : C) = 1 := by
    simpa only [mul_inv_rev, inv_inv] using Units.mul_inv (q * r⁻¹)
  constructor
  · apply hu.mul_left_inj.mp
    linear_combination (↑(q * r⁻¹) : C) * (hS - hs) - ψ (Q x (H).1.1) * ψ (M sx) * ht
  · apply ((r * q⁻¹).isUnit.mul hu).mul_right_inj.mp
    rw [mul_zero]
    exact hV.trans hY

include D hk hz hψ hJ hx hy hq hL hM hu in
/-- On the opposite original conic branch, scale/X has the inverse smooth character. -/
theorem splitDepthOriginalFraction_second (h0 : ψ (L yx) = -ψ (φ a)) :
    ψ (M sx) = (↑(r * q⁻¹) : C) * ψ (L sx) ∧ ψ (M yx) = -ψ (φ a) := by
  obtain ⟨⟨hs, hS⟩, ⟨hv, hV⟩⟩ := splitDepthOriginalFraction_ratios d b f φ z hI hz L M hL hM
  have hs := congrArg ψ hs
  have hS := congrArg ψ hS
  have hv := congrArg ψ hv
  have hV := congrArg ψ hV
  simp only [map_mul] at hs hS hv hV
  have hzero : ψ (Q (y + a * x)
      ((I).add_mem (H).1.2 ((I).mul_mem_left a (H).1.1))) = 0 := by
    rw [quotient_add_mul I φ z hI hz x y a (H).1.1 (H).1.2, map_add, map_mul, ← hv, h0]
    ring
  obtain ⟨hY, hX⟩ := splitDepthExceptional_second_horizontal
    D d hk b f φ z hI hz ψ hψ hJ r q hx hy hq hzero
  rw [quotient_add_mul I φ z hI hz X Y a (H).2.1 (H).2.2, map_add, map_mul] at hY
  rw [hX] at hS hV hY
  have ht : (↑(r * q⁻¹) : C) * (↑(q * r⁻¹) : C) = 1 := by
    simpa only [mul_inv_rev, inv_inv] using Units.mul_inv (r * q⁻¹)
  constructor
  · apply hu.mul_left_inj.mp
    linear_combination (↑(r * q⁻¹) : C) * (hS - hs) - ψ (Q x (H).1.1) * ψ (M sx) * ht
  · apply ((q * r⁻¹).isUnit.mul hu).mul_right_inj.mp
    linear_combination hV + hY

end FLT.Mazur.WeierstrassIntegralChart
