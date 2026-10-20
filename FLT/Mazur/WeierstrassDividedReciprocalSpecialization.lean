/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedReciprocalOutput
public import FLT.Mazur.WeierstrassIntegralZeroSection

/-!
# Equal-abscissa reciprocal specializations are the original infinity point

The statements apply after every algebra map out of the genuine reciprocal
source. In particular, equality of abscissae need only hold after specialization.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory WeierstrassCurve
namespace FLT.Mazur.WeierstrassDilatation
open WeierstrassIntegralAddition
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S B : Type u} [CommRing R] [CommRing S] [CommRing B]
  [Algebra R S] [Algebra R B] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (a c : Coordinate W s b3 b4 b6 →ₐ[R] S)
local notation "T" => DividedReciprocalRing W s b3 b4 b6 a c
local notation "O" => DividedReciprocalOutputRing W s b3 b4 b6 a c
local notation "j" => IsScalarTower.toAlgHom R S T
local notation "v" => dividedReciprocalCoordinates W s b3 b4 b6 a c
local notation "m" => dividedReciprocalSlope W s b3 b4 b6 a c

/-- Equal divided abscissae force zero reciprocal slope after any specialization. -/
theorem dividedReciprocalSpecialization_slope (f : T →ₐ[R] B)
    (hx : f (j (a (x W s b3 b4 b6))) = f (j (c (x W s b3 b4 b6)))) : f m = 0 := by
  have hu := (dividedReciprocal_difference_isUnit W s b3 b4 b6 a c).map f
  have hl := congrArg f (dividedReciprocalSlope_line W s b3 b4 b6 a c)
  apply hu.mul_left_inj.mp
  simpa only [map_mul, map_sub, AlgHom.comp_apply, hx, sub_self, zero_mul] using hl

/-- Every such specialization has homogeneous coordinates exactly [0,-1,0]. -/
theorem dividedReciprocalSpecialization_coordinates (f : T →ₐ[R] B)
    (hx : f (j (a (x W s b3 b4 b6))) = f (j (c (x W s b3 b4 b6)))) (i : Fin 3) :
    f (v i) = ![0, -1, 0] i := by
  have hm := dividedReciprocalSpecialization_slope W s b3 b4 b6 a c f hx
  fin_cases i <;>
    simp [dividedReciprocalCoordinates, reciprocalXYZ, reciprocalH, hm]

variable (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
  (e : DividedReciprocalOutputRing W s b3 b4 b6 a c →ₐ[R] B)
local notation "fe" => e.comp (IsScalarTower.toAlgHom R T O)

/-- Normalization gives the actual original infinity evaluation on every coordinate. -/
theorem dividedReciprocalSpecialization_output
    (hx : fe (j (a (x W s b3 b4 b6))) = fe (j (c (x W s b3 b4 b6)))) :
    e.comp (dividedReciprocalOutput W s b3 b4 b6 a c h3 h4 h6) =
      WeierstrassIntegralChart.chartInfinityEvaluation W := by
  have hv (i) : e (algebraMap T O (v i)) = ![0, -1, 0] i :=
    dividedReciprocalSpecialization_coordinates W s b3 b4 b6 a c fe hx i
  have hn := congrArg e (dividedReciprocalOutput_normalize W s b3 b4 b6 a c)
  simp only [map_mul, map_one, hv] at hn
  apply WeierstrassIntegralChart.hom_ext
  intro i
  simp only [AlgHom.comp_apply, dividedReciprocalOutput_coord, map_mul, hv]
  fin_cases i
  · simp
  · simpa [WeierstrassIntegralChart.chartInfinityEvaluation_coord] using hn
  · simp

/-- The normalized original curve output is its actual zero section over the same base. -/
theorem dividedReciprocalSpecialization_toCurve
    (hx : fe (j (a (x W s b3 b4 b6))) = fe (j (c (x W s b3 b4 b6)))) :
    Spec.map (CommRingCat.ofHom e.toRingHom) ≫
        dividedReciprocalToCurve W s b3 b4 b6 a c h3 h4 h6 =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫
        WeierstrassIntegralChart.integralCurveZero W := by
  rw [dividedReciprocalToCurve, ← Category.assoc, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    (e.comp (dividedReciprocalOutput W s b3 b4 b6 a c h3 h4 h6)).toRingHom) ≫ _ = _
  rw [dividedReciprocalSpecialization_output W s b3 b4 b6 a c h3 h4 h6 e hx,
    WeierstrassIntegralChart.chartInfinityEvaluation_base,
    WeierstrassIntegralChart.integralCurveZero, ← Category.assoc, ← Spec.map_comp]
  rfl

end FLT.Mazur.WeierstrassDilatation
