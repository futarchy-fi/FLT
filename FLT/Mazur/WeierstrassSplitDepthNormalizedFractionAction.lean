/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitDepthOriginalFractionAction
public import FLT.Mazur.WeierstrassSplitDepthAffineParameters

/-!
# Original fraction action in the normalized smooth parameter

The actual smooth affine/Y overlap constructs the slope units. Consequently
the original horizontal conic coordinates transform by the normalized Laurent
parameter and its inverse without assuming affine slope formulas.
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
local notation "Q" => quotient I φ z hI

open WeierstrassModificationReesCoordinates BlowupFractionChart
local notation "I₀" => modificationChartCenter W (π ^ k) 2
local notation "sx" => horizontalScale W (π ^ k)
local notation "yx" => horizontalVertical W (π ^ k)
variable (L M : chart (modificationChartCenter W (π ^ k) 2) (coord W 2 0) →+* B)
  (hL : ∀ t, L (algebraMap (Coordinate W 2) _ t) = φ (f (ordinaryInputRight W b t)))
  (hM : ∀ t, M (algebraMap (Coordinate W 2) _ t) = φ (f (ordinaryChartAddition W b t)))

variable (hu : IsUnit (ψ (quotient
    ((modificationChartCenter W (π ^ k) 2).map (f.comp (ordinaryInputRight W b)).toRingHom)
    φ z hI (f (ordinaryInputRight W b (coord W 2 0)))
    (splitDepthExceptional_coordinates_mem d b f).1.1)))

variable (hdepth : 0 < depth) (v : Fin 3 → C)
  (hv : ∀ i, (ψ.comp φ) (f (ordinaryInputLeft W b (coord W 2 i))) =
    (ψ.comp φ) (f (ordinaryInputLeft W b (coord W 2 1))) * v i)
  (τ : Cˣ) (hτ : (τ : C) = 1 + ψ (φ (algebraMap R S W.a₁)) * v 0)

include D hk hz hψ hJ hL hM hu hdepth hv hτ in
/-- Both original conic branches use the actual normalized smooth parameter, with opposite signs. -/
theorem splitDepthOriginalFraction_normalized :
    (ψ (L yx) = 0 → ψ (M sx) = (τ : C) * ψ (L sx) ∧ ψ (M yx) = 0) ∧
    (ψ (L yx) = -ψ (φ a) →
      ψ (M sx) = (↑τ⁻¹ : C) * ψ (L sx) ∧ ψ (M yx) = -ψ (φ a)) := by
  obtain ⟨r, q, hq, hx, hy, hr⟩ := splitDepthAffine_exists_normalized_units
    D hdepth (f.comp (ordinaryInputLeft W b)) (ψ.comp φ) hJ v hv
  have he : τ = q * r⁻¹ := by
    apply Units.ext
    rw [hτ, hr, Units.val_mul, hq]
    change 1 + ψ (φ a) * (↑r⁻¹ : C) = ((r : C) + ψ (φ a)) * (↑r⁻¹ : C)
    linear_combination -(Units.mul_inv r)
  constructor
  · intro h0
    rw [he]
    exact splitDepthOriginalFraction_first D d hk b f φ z hI hz ψ hψ hJ
      r q hx hy hq L M hL hM hu h0
  · intro h0
    rw [he, mul_inv_rev, inv_inv]
    exact splitDepthOriginalFraction_second D d hk b f φ z hI hz ψ hψ hJ
      r q hx hy hq L M hL hM hu h0

end FLT.Mazur.WeierstrassIntegralChart
