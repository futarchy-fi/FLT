/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitDepthNormalizedQuotientAction
public import FLT.Mazur.WeierstrassDilatationOriginalQuotients
public import FLT.Mazur.RegularCenterQuotientLinear

/-!
# The terminal divided coordinates have the actual reciprocal characters

The original ordinary addition map determines the residue action on both
divided tangent coordinates. The proof cancels the scale only before reduction.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassIntegralChart
open IsLocalRing WeierstrassDividedDepth RegularCenter
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S B C : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  [CommRing S] [Algebra R S] [CommRing B] [Algebra R B] [CommRing C]
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
variable (φ : S →ₐ[R] B)
local notation "z" => algebraMap R B (π ^ k)
variable (hz : IsRegular (algebraMap R B (π ^ k)))
  (L M : WeierstrassDilatation.Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] B)
local notation "orig" => WeierstrassDilatation.fromOriginal W (π ^ k)
  d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6
variable (hL : L.comp (WeierstrassDilatation.fromOriginal W (π ^ k)
    d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6) =
      φ.comp (f.comp (ordinaryInputRight W b)))
  (hM : M.comp (WeierstrassDilatation.fromOriginal W (π ^ k)
    d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6) =
      φ.comp (f.comp (ordinaryChartAddition W b)))
local notation "hI" => WeierstrassDilatation.originalDividedPoint_center W (π ^ k)
  d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6 (f.comp (ordinaryInputRight W b)) φ L hL
variable (ψ : B →+* C) (hψ : ψ (algebraMap R B (π ^ k)) = 0)
  (hJ : (maximalIdeal R).map (algebraMap R S) ≤ RingHom.ker (ψ.comp φ.toRingHom))
local notation "dx" => WeierstrassDilatation.x W (π ^ k) d.b3 d.b4 d.b6
local notation "dy" => WeierstrassDilatation.y W (π ^ k) d.b3 d.b4 d.b6

local notation "Q" => quotient I φ.toRingHom z hI

variable (hdepth : 0 < depth) (v : Fin 3 → C)
  (hv : ∀ i, (ψ.comp φ.toRingHom) (f (ordinaryInputLeft W b (coord W 2 i))) =
    (ψ.comp φ.toRingHom) (f (ordinaryInputLeft W b (coord W 2 1))) * v i)
  (τ : Cˣ) (hτ : (τ : C) = 1 + ψ (φ (algebraMap R S W.a₁)) * v 0)

include D hk hz hψ hJ hdepth hv hτ hL hM in
/-- Both original divided tangent coordinates scale by the actual smooth parameter. -/
theorem splitDepthDivided_normalized :
    ψ (M dy) = (τ : C) * ψ (L dy) ∧
      ψ (M dy + algebraMap R B W.a₁ * M dx) =
        (↑τ⁻¹ : C) * ψ (L dy + algebraMap R B W.a₁ * L dx) := by
  have h := splitDepthExceptional_normalized D d hk b f φ.toRingHom z hI hz ψ hψ hJ
    hdepth v hv τ hτ
  have qx := WeierstrassDilatation.originalDividedPoint_quotient_x W (π ^ k)
    d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6 (f.comp (ordinaryInputRight W b))
    φ L hL I hz hI (H).1.1
  have qy := WeierstrassDilatation.originalDividedPoint_quotient_y W (π ^ k)
    d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6 (f.comp (ordinaryInputRight W b))
    φ L hL I hz hI (H).1.2
  have qX := WeierstrassDilatation.originalDividedPoint_quotient_x W (π ^ k)
    d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6 (f.comp (ordinaryChartAddition W b))
    φ M hM I hz hI (H).2.1
  have qY := WeierstrassDilatation.originalDividedPoint_quotient_y W (π ^ k)
    d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6 (f.comp (ordinaryChartAddition W b))
    φ M hM I hz hI (H).2.2
  simp only [AlgHom.comp_apply] at qx qy qX qY
  rw [quotient_add_mul I φ.toRingHom z hI hz X Y a (H).2.1 (H).2.2,
    quotient_add_mul I φ.toRingHom z hI hz x y a (H).1.1 (H).1.2,
    qx, qy, qX, qY] at h
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes] at h
  exact h

end FLT.Mazur.WeierstrassIntegralChart
