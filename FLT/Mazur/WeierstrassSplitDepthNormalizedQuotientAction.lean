/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitDepthExceptionalScaling
public import FLT.Mazur.WeierstrassSplitDepthAffineParameters

/-!
# Both exceptional quotient characters in the original normalized smooth parameter

The conormal characters hold without imposing either zero-slope branch.
This retains the two nonzero tangent coordinates at terminal equality depth.
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

variable (hdepth : 0 < depth) (v : Fin 3 → C)
  (hv : ∀ i, (ψ.comp φ) (f (ordinaryInputLeft W b (coord W 2 i))) =
    (ψ.comp φ) (f (ordinaryInputLeft W b (coord W 2 1))) * v i)
  (τ : Cˣ) (hτ : (τ : C) = 1 + ψ (φ (algebraMap R S W.a₁)) * v 0)

include D hk hz hψ hJ hdepth hv hτ in
/-- Both actual divided tangent quotients retain the normalized reciprocal characters. -/
theorem splitDepthExceptional_normalized :
    ψ (Q Y (H).2.2) = (τ : C) * ψ (Q y (H).1.2) ∧
      ψ (Q (Y + a * X) ((I).add_mem (H).2.2 ((I).mul_mem_left a (H).2.1))) =
        (↑τ⁻¹ : C) *
          ψ (Q (y + a * x) ((I).add_mem (H).1.2 ((I).mul_mem_left a (H).1.1))) := by
  obtain ⟨r, q, hq, hx, hy, hr⟩ := splitDepthAffine_exists_normalized_units
    D hdepth (f.comp (ordinaryInputLeft W b)) (ψ.comp φ) hJ v hv
  have he : τ = q * r⁻¹ := by
    apply Units.ext
    rw [hτ, hr, Units.val_mul, hq]
    change 1 + ψ (φ a) * (↑r⁻¹ : C) = ((r : C) + ψ (φ a)) * (↑r⁻¹ : C)
    linear_combination -(Units.mul_inv r)
  rw [he, mul_inv_rev, inv_inv]
  exact ⟨splitDepthExceptional_first_scaling D d hk b f φ z hI hz ψ hψ hJ r q hx hy hq,
    splitDepthExceptional_second_scaling D d hk b f φ z hI hz ψ hψ hJ r q hx hy hq⟩

include D hk hz hψ hJ hdepth hv hτ in
/-- Translation preserves the product of the two original tangent quotients. -/
theorem splitDepthExceptional_normalized_product :
    ψ (Q Y (H).2.2) *
        ψ (Q (Y + a * X) ((I).add_mem (H).2.2 ((I).mul_mem_left a (H).2.1))) =
      ψ (Q y (H).1.2) *
        ψ (Q (y + a * x) ((I).add_mem (H).1.2 ((I).mul_mem_left a (H).1.1))) := by
  obtain ⟨h₁, h₂⟩ := splitDepthExceptional_normalized D d hk b f φ z hI hz ψ hψ hJ
    hdepth v hv τ hτ
  rw [h₁, h₂]
  calc
    _ = ((τ : C) * (↑τ⁻¹ : C)) * (ψ (Q y (H).1.2) *
        ψ (Q (y + a * x) ((I).add_mem (H).1.2 ((I).mul_mem_left a (H).1.1)))) := by ring
    _ = _ := by rw [Units.mul_inv, one_mul]

end FLT.Mazur.WeierstrassIntegralChart
