/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedReciprocalSource

/-!
# The divided reciprocal output in the original infinity chart

Invert the homogeneous output ordinate and normalize it to one. This gives
an actual morphism to the unchanged original cubic, with its original base
map, and does not require the scale to be regular or either input to be smooth.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory WeierstrassCurve
namespace FLT.Mazur.WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (a c : Coordinate W s b3 b4 b6 →ₐ[R] S)
local notation "T" => DividedReciprocalRing W s b3 b4 b6 a c
local notation "v" => dividedReciprocalCoordinates W s b3 b4 b6 a c

/-- The actual output chart open, obtained by inverting the homogeneous ordinate. -/
def DividedReciprocalOutputRing :=
  Localization.Away (dividedReciprocalCoordinates W s b3 b4 b6 a c 1)
local notation "O" => DividedReciprocalOutputRing W s b3 b4 b6 a c

instance dividedReciprocalOutputCommRing : CommRing O :=
  inferInstanceAs (CommRing (Localization.Away (v 1)))
instance dividedReciprocalOutputAlgebraSource : Algebra T O :=
  inferInstanceAs (Algebra T (Localization.Away (v 1)))
instance dividedReciprocalOutputAlgebra : Algebra R O :=
  inferInstanceAs (Algebra R (Localization.Away (v 1)))
instance dividedReciprocalOutputTower : IsScalarTower R T O :=
  inferInstanceAs (IsScalarTower R T (Localization.Away (v 1)))
instance dividedReciprocalOutputLocalization : IsLocalization.Away (v 1) O :=
  inferInstanceAs (IsLocalization.Away (v 1) (Localization.Away (v 1)))
attribute [irreducible] DividedReciprocalOutputRing

/-- The unit output ordinate on the new principal open. -/
def dividedReciprocalOutputUnit : Oˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := O) (v 1)).unit

/-- The normalizing factor cancels the actual output ordinate. -/
theorem dividedReciprocalOutput_normalize :
    (↑(dividedReciprocalOutputUnit W s b3 b4 b6 a c)⁻¹ : O) * algebraMap T O (v 1) = 1 :=
  Units.inv_mul_eq_one.mpr (IsLocalization.Away.algebraMap_isUnit (S := O) (v 1)).unit_spec

variable (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)

include h3 h4 h6 in
/-- The homogeneous equation survives the actual output localization. -/
theorem dividedReciprocalOutput_equation :
    (W.map (algebraMap R O)).toProjective.Equation (algebraMap T O ∘ v) := by
  have h := (dividedReciprocalCoordinates_equation W s b3 b4 b6 a c h3 h4 h6).map
    (algebraMap T O)
  change ((W.map (algebraMap R T)).map (algebraMap T O)).toProjective.Equation
    (algebraMap T O ∘ v) at h
  have he : (W.map (algebraMap R T)).map (algebraMap T O) = W.map (algebraMap R O) := by
    ext <;> exact (IsScalarTower.algebraMap_apply R T O _).symm
  rw [he] at h
  exact h

/-- The constructed normalized algebra map into the original chart containing infinity. -/
def dividedReciprocalOutput : WeierstrassIntegralChart.Coordinate W 1 →ₐ[R] O :=
  WeierstrassIntegralChart.evaluation W 1
    ((↑(dividedReciprocalOutputUnit W s b3 b4 b6 a c)⁻¹ : O) • (algebraMap T O ∘ v))
    (((W.map (algebraMap R O)).toProjective.equation_smul _ (Units.isUnit _)).mpr
      (dividedReciprocalOutput_equation W s b3 b4 b6 a c h3 h4 h6))
    (dividedReciprocalOutput_normalize W s b3 b4 b6 a c)

/-- Every normalized coordinate is the actual homogeneous coordinate divided by its ordinate. -/
theorem dividedReciprocalOutput_coord (i : Fin 3) :
    dividedReciprocalOutput W s b3 b4 b6 a c h3 h4 h6
        (WeierstrassIntegralChart.coord W 1 i) =
      (↑(dividedReciprocalOutputUnit W s b3 b4 b6 a c)⁻¹ : O) * algebraMap T O (v i) :=
  WeierstrassIntegralChart.evaluation_coord W 1 _ _ _ i

/-- The actual reciprocal map to the unchanged original projective cubic. -/
def dividedReciprocalToCurve : Spec (.of O) ⟶ WeierstrassIntegralChart.integralCurve W :=
  Spec.map (CommRingCat.ofHom (dividedReciprocalOutput W s b3 b4 b6 a c h3 h4 h6).toRingHom) ≫
    WeierstrassIntegralChart.integralCurveChart W 1

/-- The newly constructed infinity-chart map retains the original coefficient morphism. -/
@[reassoc] theorem dividedReciprocalToCurve_structure :
    dividedReciprocalToCurve W s b3 b4 b6 a c h3 h4 h6 ≫
        WeierstrassIntegralChart.integralCurveStructure W =
      Spec.map (CommRingCat.ofHom (algebraMap R O)) :=
  WeierstrassIntegralChart.integralChartPoint_structure W 1 _ _ _

end FLT.Mazur.WeierstrassDilatation
