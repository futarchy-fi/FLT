/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedCrossDepthReciprocalSecant
public import FLT.Mazur.WeierstrassDividedReciprocalOutput
public import FLT.Mazur.WeierstrassScaledChartComparison

/-!
# Normalized reciprocal and secant outputs across divided depths

The original inputs determine an invertible homogeneous scale. The actual
normalized reciprocal output therefore agrees with the other-depth secant
output as a morphism into the unchanged projective cubic.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S S' B : Type u} [CommRing R] [CommRing S] [CommRing S'] [CommRing B]
  [Algebra R S] [Algebra R S'] [Algebra R B]
  (W : WeierstrassCurve R) (s b3 b4 b6 t c3 c4 c6 : R)
  (a c : Coordinate W s b3 b4 b6 →ₐ[R] S)
  (a₂ c₂ : Coordinate W t c3 c4 c6 →ₐ[R] S')
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
  (k3 : W.a₃ = t * c3) (k4 : W.a₄ = t * c4) (k6 : W.a₆ = t ^ 2 * c6)
  (e : DividedReciprocalOutputRing W s b3 b4 b6 a c →ₐ[R] B)
  (f : DividedSecantRing W t c3 c4 c6 a₂ c₂ →ₐ[R] B)
local notation "T" => DividedReciprocalRing W s b3 b4 b6 a c
local notation "O" => DividedReciprocalOutputRing W s b3 b4 b6 a c
local notation "et" => e.comp (IsScalarTower.toAlgHom R T O)
local notation "m" => et (dividedReciprocalSlope W s b3 b4 b6 a c)
local notation "q" => e (↑(dividedReciprocalOutputUnit W s b3 b4 b6 a c)⁻¹ : O) * m ^ 3
variable
  (ha : (((e.comp (IsScalarTower.toAlgHom R
      (DividedReciprocalRing W s b3 b4 b6 a c)
      (DividedReciprocalOutputRing W s b3 b4 b6 a c))).comp
        (IsScalarTower.toAlgHom R S (DividedReciprocalRing W s b3 b4 b6 a c))).comp a).comp
          (fromOriginal W s b3 b4 b6 h3 h4 h6) =
    ((f.comp (IsScalarTower.toAlgHom R S'
      (DividedSecantRing W t c3 c4 c6 a₂ c₂))).comp a₂).comp
        (fromOriginal W t c3 c4 c6 k3 k4 k6))
  (hc : (((e.comp (IsScalarTower.toAlgHom R
      (DividedReciprocalRing W s b3 b4 b6 a c)
      (DividedReciprocalOutputRing W s b3 b4 b6 a c))).comp
        (IsScalarTower.toAlgHom R S (DividedReciprocalRing W s b3 b4 b6 a c))).comp c).comp
          (fromOriginal W s b3 b4 b6 h3 h4 h6) =
    ((f.comp (IsScalarTower.toAlgHom R S'
      (DividedSecantRing W t c3 c4 c6 a₂ c₂))).comp c₂).comp
        (fromOriginal W t c3 c4 c6 k3 k4 k6))
  (hs : IsRegular (algebraMap R B s))

include ha hc hs in
/-- The actual normalized output scale is a unit on the cross-depth overlap. -/
theorem dividedCrossDepthReciprocalSecantOutput_scale_isUnit : IsUnit q := by
  have hm : IsUnit m := isUnit_iff_exists_inv.mpr ⟨_,
    dividedCrossDepthReciprocalSecant_inverse W s b3 b4 b6 t c3 c4 c6 a c a₂ c₂
      h3 h4 h6 k3 k4 k6 et f ha hc hs⟩
  exact ((Units.isUnit _).map e).mul (hm.pow 3)

local notation "A" => f.comp (dividedSecantOutput W t c3 c4 c6 a₂ c₂ k3 k4 k6)
local notation "C" => e.comp (dividedReciprocalOutput W s b3 b4 b6 a c h3 h4 h6)

include ha hc hs in
/-- Each normalized original coordinate has the same constructed scale across the two depths. -/
theorem dividedCrossDepthReciprocalSecantOutput_scaled (i : Fin 3) :
    C (WeierstrassIntegralChart.coord W 1 i) =
      q * A (WeierstrassIntegralChart.coord W 2 i) := by
  simp only [AlgHom.comp_apply, dividedReciprocalOutput_coord, map_mul]
  change e (↑(dividedReciprocalOutputUnit W s b3 b4 b6 a c)⁻¹ : O) *
    et (dividedReciprocalCoordinates W s b3 b4 b6 a c i) = _
  rw [dividedCrossDepthReciprocalSecant_scaled W s b3 b4 b6 t c3 c4 c6 a c a₂ c₂
    h3 h4 h6 k3 k4 k6 et f ha hc hs]
  exact (mul_assoc _ _ _).symm

include ha hc hs in
/-- The actual outputs agree in the original cubic despite independent input scales. -/
theorem dividedCrossDepthReciprocalSecantOutput_toCurve :
    Spec.map (CommRingCat.ofHom e.toRingHom) ≫
        dividedReciprocalToCurve W s b3 b4 b6 a c h3 h4 h6 =
      Spec.map (CommRingCat.ofHom f.toRingHom) ≫
        dividedSecantToCurve W t c3 c4 c6 a₂ c₂ k3 k4 k6 := by
  let hu := dividedCrossDepthReciprocalSecantOutput_scale_isUnit
    W s b3 b4 b6 t c3 c4 c6 a c a₂ c₂ h3 h4 h6 k3 k4 k6 e f ha hc hs
  let hscaled := dividedCrossDepthReciprocalSecantOutput_scaled
    W s b3 b4 b6 t c3 c4 c6 a c a₂ c₂ h3 h4 h6 k3 k4 k6 e f ha hc hs
  let k := WeierstrassIntegralChart.scaledChartLift W 2 1 A C q hu hscaled
  rw [dividedReciprocalToCurve, dividedSecantToCurve, ← Category.assoc,
    ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  apply WeierstrassIntegralChart.integralCurve_output_eq W 1 2 _ _
    (Spec.map (CommRingCat.ofHom k.toRingHom))
  · change Spec.map (CommRingCat.ofHom k.toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (WeierstrassIntegralChart.overlapRestriction W 1 2).toRingHom) = _
    rw [← Spec.map_comp]
    exact congrArg (fun h => Spec.map (CommRingCat.ofHom h.toRingHom))
      (WeierstrassIntegralChart.scaledChartLift_restriction W 2 1 A C q hu hscaled)
  · rw [← Spec.map_comp]
    exact congrArg (fun h => Spec.map (CommRingCat.ofHom h.toRingHom))
      (WeierstrassIntegralChart.scaledChartLift_transition W 2 1 A C q hu hscaled)

end FLT.Mazur.WeierstrassDilatation
