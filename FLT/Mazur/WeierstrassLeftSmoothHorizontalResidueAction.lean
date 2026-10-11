/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLeftSmoothHorizontalActionPresentation
public import FLT.Mazur.WeierstrassSplitDepthNormalizedFractionAction

/-!
# Residue conic coordinates of the named smooth action lift

The actual horizontal action cover satisfies the regular-center presentation
used by the integral conormal calculation. Its input horizontal quotient is
one, so no extra invertibility assumption is needed on the residue source.
The normalized smooth parameter gives both original branch orientations.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  (W : WeierstrassCurve R) (π : R) {depth k : ℕ} (b3 b4 b6 : R)
  (D : SplitNodeDepth W π depth) (d : WeierstrassDividedDepth.Data W π k)
  (hk : 2 * k ≤ depth) (hdepth : 0 < depth)
  (h3 : W.a₃ = (π ^ k) * b3) (h4 : W.a₄ = (π ^ k) * b4) (h6 : W.a₆ = (π ^ k) * b6)
  {S : Type u} [CommRing S] [Algebra R S]
  (p : Spec (.of S) ⟶ (integralSmoothOpen W).toScheme) (α β : Coordinate W 2 →+* S)
  (hp : p ≫ integralSmoothStructure W =
    (Spec.map (CommRingCat.ofHom β) ≫ integralCurveChart W 2) ≫ integralCurveStructure W)
  (hα : Spec.map (CommRingCat.ofHom α) ≫ integralCurveChart W 2 =
    leftSmoothPointAddition W p (Spec.map (CommRingCat.ofHom β) ≫ integralCurveChart W 2) hp)

local notation "I" => modificationChartCenter W (π ^ k) 2
local notation "x" => coord W 2 0
local notation "hx" => WeierstrassModificationReesCoordinates.centerGenerators_mem W (π ^ k) 1
variable (ψ : BlowupFractionChart.chart (modificationChartCenter W (π ^ k) 2) (coord W 2 0) →+* S)
  (hβ : β = ψ.comp
    (algebraMap (Coordinate W 2)
      (BlowupFractionChart.chart (modificationChartCenter W (π ^ k) 2) (coord W 2 0))))
  (hflat : RingHom.Flat
    (R := BlowupFractionChart.chart (modificationChartCenter W (π ^ k) 2) (coord W 2 0)) (S := S) ψ)

open RegularCenter BlowupFractionChart
local notation "z" => ψ (denominator I x)
local notation "O" => LeftSmoothFractionActionOpen W (π ^ k) b3 b4 b6
  h3 h4 h6 p α β hp hα x hx ψ hβ 1
local notation "φ" => algebraMap S O

open WeierstrassModificationReesCoordinates IsLocalRing
local notation "L" => leftSmoothHorizontalInputLift W (π ^ k) b3 b4 b6
  h3 h4 h6 p α β hp hα ψ hβ
local notation "M" => leftSmoothFractionActionLift W (π ^ k) b3 b4 b6
  h3 h4 h6 p α β hp hα x hx ψ hβ hflat 1
local notation "sx" => horizontalScale W (π ^ k)
local notation "yx" => horizontalVertical W (π ^ k)
variable (b : Bool) (f : additionChartRing W (ordinaryIndex b) →ₐ[R] S)
  (hβf : β = (f.comp (ordinaryInputRight W b)).toRingHom)
  (hαf : α = (f.comp (ordinaryChartAddition W b)).toRingHom)
  {C : Type u} [CommRing C]

include D d hk hdepth hflat hβf hαf in
/-- On the named action cover, both initial conic slopes and parameter characters are exact. -/
theorem leftSmoothHorizontalAction_normalized (e : O →+* C) (he : e (φ z) = 0)
    (hJ : (maximalIdeal R).map (algebraMap R S) ≤ RingHom.ker (e.comp φ))
    (v : Fin 3 → C)
    (hv : ∀ i, e (φ (f (ordinaryInputLeft W b (coord W 2 i)))) =
      e (φ (f (ordinaryInputLeft W b (coord W 2 1)))) * v i)
    (τ : Cˣ) (hτ : (τ : C) = 1 + e (φ (algebraMap R S W.a₁)) * v 0) :
    (e (L yx) = 0 → e (M sx) = (τ : C) * e (L sx) ∧ e (M yx) = 0) ∧
    (e (L yx) = -e (φ (algebraMap R S W.a₁)) →
      e (M sx) = (↑τ⁻¹ : C) * e (L sx) ∧ e (M yx) = -e (φ (algebraMap R S W.a₁))) := by
  have hi : ((I).map (f.comp (ordinaryInputRight W b)).toRingHom).map φ =
      Ideal.span {φ z} := by
    rw [← hβf]
    exact leftSmoothHorizontalInput_principal W (π ^ k) b3 b4 b6
      h3 h4 h6 p α β hp hα ψ hβ
  have hr := leftSmoothHorizontalInput_regular W (π ^ k) b3 b4 b6
    h3 h4 h6 p α β hp hα ψ hβ hflat
  have hL (t : Coordinate W 2) : L (algebraMap _ _ t) =
      φ (f (ordinaryInputRight W b t)) := by
    exact (leftSmoothHorizontalInputLift_base W (π ^ k) b3 b4 b6
      h3 h4 h6 p α β hp hα ψ hβ t).trans (congrArg φ (DFunLike.congr_fun hβf t))
  have hM (t : Coordinate W 2) : M (algebraMap _ _ t) =
      φ (f (ordinaryChartAddition W b t)) := by
    exact (leftSmoothFractionActionLift_base W (π ^ k) b3 b4 b6
      h3 h4 h6 p α β hp hα x hx ψ hβ hflat 1 t).trans
        (congrArg φ (DFunLike.congr_fun hαf t))
  have hq : quotient ((I).map (f.comp (ordinaryInputRight W b)).toRingHom)
      φ (φ z) hi (f (ordinaryInputRight W b x))
      (splitDepthExceptional_coordinates_mem d b f).1.1 = 1 := by
    symm
    apply quotient_unique _ _ _ _ hr
    rw [mul_one]
    exact congrArg φ ((leftSmoothHorizontalInput_denominator W (π ^ k) β ψ hβ).symm.trans
      (DFunLike.congr_fun hβf x))
  exact splitDepthOriginalFraction_normalized D d hk b f φ (φ z) hi hr e he hJ
    L M hL hM (by rw [hq, map_one]; exact isUnit_one) hdepth v hv τ hτ

end FLT.Mazur.WeierstrassIntegralChart
