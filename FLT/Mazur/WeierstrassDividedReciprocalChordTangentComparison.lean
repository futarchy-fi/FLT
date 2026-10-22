/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedReciprocalChordTangentFormula
public import FLT.Mazur.WeierstrassDividedReciprocalChordOutput
public import FLT.Mazur.WeierstrassScaledChartComparison

/-!
# The normalized reciprocal chord and tangent maps agree on their actual overlap

The unit homogeneous scale constructs a genuine Y/Z output-overlap lift.
Its two restrictions give equality in the unchanged original projective
cubic over every common algebra of the input domains.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S B : Type u} [CommRing R] [CommRing S] [CommRing B]
  [Algebra R S] [Algebra R B] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (a c : Coordinate W s b3 b4 b6 →ₐ[R] S)
  (e : DividedReciprocalChordOutputRing W s b3 b4 b6 a c →ₐ[R] B)
  (f : DividedTangentRing W s b3 b4 b6 a c →ₐ[R] B)
local notation "T" => DividedReciprocalChordRing W s b3 b4 b6 a c
local notation "O" => DividedReciprocalChordOutputRing W s b3 b4 b6 a c
local notation "V" => DividedTangentRing W s b3 b4 b6 a c
local notation "et" => e.comp (IsScalarTower.toAlgHom R T O)
local notation "m" => et (dividedReciprocalChordSlope W s b3 b4 b6 a c)
local notation "q" => e (↑(dividedReciprocalChordOutputUnit W s b3 b4 b6 a c)⁻¹ : O) * m ^ 3
variable
  (hb : (e.comp (IsScalarTower.toAlgHom R
      (DividedReciprocalChordRing W s b3 b4 b6 a c)
      (DividedReciprocalChordOutputRing W s b3 b4 b6 a c))).comp
        (IsScalarTower.toAlgHom R S (DividedReciprocalChordRing W s b3 b4 b6 a c)) =
    f.comp (IsScalarTower.toAlgHom R S (DividedTangentRing W s b3 b4 b6 a c)))

include hb in
/-- The actual normalized output scale is invertible on the whole common source. -/
theorem dividedReciprocalChordTangentOutput_scale_isUnit : IsUnit q := by
  have hm : IsUnit m := isUnit_iff_exists_inv.mpr ⟨_,
    dividedReciprocalChordTangent_inverse W s b3 b4 b6 a c et f
      (congrArg (fun k => k.comp a) hb) (congrArg (fun k => k.comp c) hb)⟩
  exact ((Units.isUnit _).map e).mul (hm.pow 3)

variable (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
local notation "A" => f.comp (dividedTangentOutput W s b3 b4 b6 a c h3 h4 h6)
local notation "C" => e.comp (dividedReciprocalChordOutput W s b3 b4 b6 a c h3 h4 h6)

include hb in
/-- The normalized original coordinates have the same common unit scale. -/
theorem dividedReciprocalChordTangentOutput_scaled (i : Fin 3) :
    C (WeierstrassIntegralChart.coord W 1 i) =
      q * A (WeierstrassIntegralChart.coord W 2 i) := by
  simp only [AlgHom.comp_apply, dividedReciprocalChordOutput_coord, map_mul]
  change e (↑(dividedReciprocalChordOutputUnit W s b3 b4 b6 a c)⁻¹ : O) *
    et (dividedReciprocalChordCoordinates W s b3 b4 b6 a c i) = _
  rw [dividedReciprocalChordTangent_scaled W s b3 b4 b6 a c et f
    (congrArg (fun k => k.comp a) hb) (congrArg (fun k => k.comp c) hb) h3 h4 h6]
  exact (mul_assoc _ _ _).symm

include hb in
/-- The two actual output morphisms to the original projective cubic coincide. -/
theorem dividedReciprocalChordTangentOutput_toCurve :
    Spec.map (CommRingCat.ofHom e.toRingHom) ≫
        dividedReciprocalChordToCurve W s b3 b4 b6 a c h3 h4 h6 =
      Spec.map (CommRingCat.ofHom f.toRingHom) ≫
        dividedTangentToCurve W s b3 b4 b6 a c h3 h4 h6 := by
  let hu := dividedReciprocalChordTangentOutput_scale_isUnit W s b3 b4 b6 a c e f hb
  let hs := dividedReciprocalChordTangentOutput_scaled W s b3 b4 b6 a c e f hb h3 h4 h6
  let k := WeierstrassIntegralChart.scaledChartLift W 2 1 A C q hu hs
  rw [dividedReciprocalChordToCurve, dividedTangentToCurve, ← Category.assoc,
    ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  apply WeierstrassIntegralChart.integralCurve_output_eq W 1 2 _ _
    (Spec.map (CommRingCat.ofHom k.toRingHom))
  · change Spec.map (CommRingCat.ofHom k.toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (WeierstrassIntegralChart.overlapRestriction W 1 2).toRingHom) = _
    rw [← Spec.map_comp]
    exact congrArg (fun h => Spec.map (CommRingCat.ofHom h.toRingHom))
      (WeierstrassIntegralChart.scaledChartLift_restriction W 2 1 A C q hu hs)
  · rw [← Spec.map_comp]
    exact congrArg (fun h => Spec.map (CommRingCat.ofHom h.toRingHom))
      (WeierstrassIntegralChart.scaledChartLift_transition W 2 1 A C q hu hs)

end FLT.Mazur.WeierstrassDilatation
