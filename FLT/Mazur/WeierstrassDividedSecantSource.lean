/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSecantFormula
public import FLT.Mazur.WeierstrassDilatationCoefficients
public import FLT.Mazur.WeierstrassDilatationMorphism

/-!
# The actual divided secant source and its original cubic output

Localize the divided abscissa difference of two arbitrary divided inputs.
The resulting morphism to the original cubic does not invert the scale and
requires neither input to belong to the original smooth locus.
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
variable (a c : Coordinate W s b3 b4 b6 →ₐ[R] S)
local notation "dx" => a (x W s b3 b4 b6) - c (x W s b3 b4 b6)

/-- The genuine principal open defined by the divided, not the original, abscissae. -/
abbrev DividedSecantRing :=
  Localization.Away (a (x W s b3 b4 b6) - c (x W s b3 b4 b6))

local notation "T" => DividedSecantRing W s b3 b4 b6 a c
local notation "j" => IsScalarTower.toAlgHom R S T

/-- The secant slope after cancelling the common scale in both input differences. -/
def dividedSecantSlope : T :=
  algebraMap S T (a (y W s b3 b4 b6) - c (y W s b3 b4 b6)) *
    IsLocalization.Away.invSelf dx

/-- The slope satisfies its divided line equation on the actual principal open. -/
theorem dividedSecantSlope_relation :
    dividedSecantSlope W s b3 b4 b6 a c *
        (((j).comp a) (x W s b3 b4 b6) - ((j).comp c) (x W s b3 b4 b6)) =
      ((j).comp a) (y W s b3 b4 b6) - ((j).comp c) (y W s b3 b4 b6) := by
  change dividedSecantSlope W s b3 b4 b6 a c *
    (algebraMap S T (a (x W s b3 b4 b6)) - algebraMap S T (c (x W s b3 b4 b6))) = _
  rw [← map_sub, dividedSecantSlope, mul_assoc, mul_comm (IsLocalization.Away.invSelf dx),
    IsLocalization.Away.mul_invSelf, mul_one, map_sub]
  rfl

local notation "W'" => (W.map (algebraMap R T)).toAffine
local notation "u₁" => ((j).comp a) (x W s b3 b4 b6)
local notation "u₂" => ((j).comp c) (x W s b3 b4 b6)
local notation "v₁" => ((j).comp a) (y W s b3 b4 b6)
local notation "v₂" => ((j).comp c) (y W s b3 b4 b6)
local notation "l" => dividedSecantSlope W s b3 b4 b6 a c
local notation "q" => algebraMap R T s

/-- The output abscissa in the unchanged original coordinates. -/
def dividedSecantX : T := (W').addX (q * u₁) (q * u₂) l

/-- The output ordinate in the unchanged original coordinates. -/
def dividedSecantY : T := (W').addY (q * u₁) (q * u₂) (q * v₁) l

variable (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)

include h3 h4 h6 in
/-- The constructed output satisfies the original cubic over the entire divided secant source. -/
theorem dividedSecant_equation :
    (W').Equation (dividedSecantX W s b3 b4 b6 a c)
      (dividedSecantY W s b3 b4 b6 a c) := by
  apply divided_secant_add_equation (W.map (algebraMap R T)) q
    (algebraMap R T b3) (algebraMap R T b4) (algebraMap R T b6)
  · simp only [map_a₃, h3, map_mul]
  · simp only [map_a₄, h4, map_mul]
  · simp only [map_a₆, h6, map_mul, map_pow]
  · exact equation_map W s b3 b4 b6 ((j).comp a)
  · exact equation_map W s b3 b4 b6 ((j).comp c)
  · change IsUnit (algebraMap S T (a (x W s b3 b4 b6)) -
      algebraMap S T (c (x W s b3 b4 b6)))
    rw [← map_sub]
    exact IsLocalization.Away.algebraMap_isUnit dx
  · exact dividedSecantSlope_relation W s b3 b4 b6 a c

/-- The actual algebra map from the original affine cubic to the divided secant domain. -/
def dividedSecantOutput : WeierstrassIntegralChart.Coordinate W 2 →ₐ[R] T :=
  WeierstrassIntegralChart.evaluation W 2
    ![dividedSecantX W s b3 b4 b6 a c, dividedSecantY W s b3 b4 b6 a c, 1]
    ((Projective.equation_some ..).mpr (dividedSecant_equation W s b3 b4 b6 a c h3 h4 h6)) rfl

/-- The output morphism keeps the original projective cubic. -/
def dividedSecantToCurve : Spec (.of T) ⟶ WeierstrassIntegralChart.integralCurve W :=
  Spec.map (CommRingCat.ofHom (dividedSecantOutput W s b3 b4 b6 a c h3 h4 h6).toRingHom) ≫
    WeierstrassIntegralChart.integralCurveChart W 2

/-- The original coefficient map is retained on this new two-input domain. -/
@[reassoc] theorem dividedSecantToCurve_structure :
    dividedSecantToCurve W s b3 b4 b6 a c h3 h4 h6 ≫
        WeierstrassIntegralChart.integralCurveStructure W =
      Spec.map (CommRingCat.ofHom (algebraMap R T)) :=
  WeierstrassIntegralChart.integralChartPoint_structure W 2 _ _ _

end FLT.Mazur.WeierstrassDilatation
