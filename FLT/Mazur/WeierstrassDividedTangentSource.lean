/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentFormula
public import FLT.Mazur.WeierstrassDilatationCoefficients
public import FLT.Mazur.WeierstrassDilatationMorphism

/-!
# The actual divided tangent source and its original cubic output

Localize the second divided slope denominator for two arbitrary inputs.
This includes equal abscissae when that denominator is a unit. The original
cubic output is constructed without inverting the original scale.
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
/-- The second divided slope denominator, before imposing either original smooth input. -/
def dividedTangentDenominator : S :=
  a (y W s b3 b4 b6) + c (y W s b3 b4 b6) +
    algebraMap R S W.a₁ * c (x W s b3 b4 b6) + algebraMap R S b3

/-- The divided chord numerator retains the original divided coefficients. -/
def dividedTangentNumerator : S :=
  algebraMap R S s * (a (x W s b3 b4 b6) ^ 2 +
    a (x W s b3 b4 b6) * c (x W s b3 b4 b6) + c (x W s b3 b4 b6) ^ 2) +
    algebraMap R S W.a₂ * (a (x W s b3 b4 b6) + c (x W s b3 b4 b6)) +
    algebraMap R S b4 - algebraMap R S W.a₁ * a (y W s b3 b4 b6)

local notation "dx" => dividedTangentDenominator W s b3 b4 b6 a c
local notation "num" => dividedTangentNumerator W s b3 b4 b6 a c

/-- The genuine principal open for the second divided slope formula. -/
def DividedTangentRing := Localization.Away (dividedTangentDenominator W s b3 b4 b6 a c)

local notation "T" => DividedTangentRing W s b3 b4 b6 a c

instance dividedTangentCommRing : CommRing T :=
  inferInstanceAs (CommRing (Localization.Away dx))

instance dividedTangentAlgebraSource : Algebra S T :=
  inferInstanceAs (Algebra S (Localization.Away dx))

instance dividedTangentAlgebra : Algebra R T :=
  inferInstanceAs (Algebra R (Localization.Away dx))

instance dividedTangentTower : IsScalarTower R S T :=
  inferInstanceAs (IsScalarTower R S (Localization.Away dx))

instance dividedTangentLocalization : IsLocalization.Away dx T :=
  inferInstanceAs (IsLocalization.Away dx (Localization.Away dx))

attribute [irreducible] DividedTangentRing

local notation "j" => IsScalarTower.toAlgHom R S T

/-- The second divided slope on its actual principal open. -/
def dividedTangentSlope : T :=
  algebraMap S T num * IsLocalization.Away.invSelf dx

/-- The constructed slope satisfies the localized chord relation. -/
theorem dividedTangentSlope_relation :
    dividedTangentSlope W s b3 b4 b6 a c * algebraMap S T dx = algebraMap S T num := by
  rw [dividedTangentSlope, mul_assoc, mul_comm (IsLocalization.Away.invSelf dx),
    IsLocalization.Away.mul_invSelf, mul_one]

local notation "W'" => (W.map (algebraMap R T)).toAffine
local notation "u₁" => ((j).comp a) (x W s b3 b4 b6)
local notation "u₂" => ((j).comp c) (x W s b3 b4 b6)
local notation "v₁" => ((j).comp a) (y W s b3 b4 b6)
local notation "v₂" => ((j).comp c) (y W s b3 b4 b6)
local notation "l" => dividedTangentSlope W s b3 b4 b6 a c
local notation "q" => algebraMap R T s

/-- The output abscissa in the unchanged original coordinates. -/
def dividedTangentX : T := (W').addX (q * u₁) (q * u₂) l

/-- The output ordinate in the unchanged original coordinates. -/
def dividedTangentY : T := (W').addY (q * u₁) (q * u₂) (q * v₁) l

variable (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)

include h3 h4 h6 in
/-- The constructed output satisfies the original cubic over the entire divided tangent source. -/
theorem dividedTangent_equation :
    (W').Equation (dividedTangentX W s b3 b4 b6 a c)
      (dividedTangentY W s b3 b4 b6 a c) := by
  apply divided_tangent_add_equation (W.map (algebraMap R T)) q
    (algebraMap R T b3) (algebraMap R T b4) (algebraMap R T b6)
  · simp only [map_a₃, h3, map_mul]
  · simp only [map_a₄, h4, map_mul]
  · simp only [map_a₆, h6, map_mul, map_pow]
  · exact equation_map W s b3 b4 b6 ((j).comp a)
  · exact equation_map W s b3 b4 b6 ((j).comp c)
  · have h := IsLocalization.Away.algebraMap_isUnit (S := T) dx
    simpa only [dividedTangentDenominator, map_a₁, map_add, map_mul,
      ← IsScalarTower.algebraMap_apply R S T, AlgHom.comp_apply,
      IsScalarTower.coe_toAlgHom'] using h
  · have h := dividedTangentSlope_relation W s b3 b4 b6 a c
    simpa only [dividedTangentDenominator, dividedTangentNumerator, map_a₁, map_a₂,
      map_add, map_mul, map_pow, map_sub, ← IsScalarTower.algebraMap_apply R S T,
      AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] using h

/-- The actual algebra map from the original affine cubic to the divided tangent domain. -/
def dividedTangentOutput : WeierstrassIntegralChart.Coordinate W 2 →ₐ[R] T :=
  WeierstrassIntegralChart.evaluation W 2
    ![dividedTangentX W s b3 b4 b6 a c, dividedTangentY W s b3 b4 b6 a c, 1]
    ((Projective.equation_some ..).mpr (dividedTangent_equation W s b3 b4 b6 a c h3 h4 h6)) rfl

/-- The output morphism keeps the original projective cubic. -/
def dividedTangentToCurve : Spec (.of T) ⟶ WeierstrassIntegralChart.integralCurve W :=
  Spec.map (CommRingCat.ofHom (dividedTangentOutput W s b3 b4 b6 a c h3 h4 h6).toRingHom) ≫
    WeierstrassIntegralChart.integralCurveChart W 2

/-- The original coefficient map is retained on this new two-input domain. -/
@[reassoc] theorem dividedTangentToCurve_structure :
    dividedTangentToCurve W s b3 b4 b6 a c h3 h4 h6 ≫
        WeierstrassIntegralChart.integralCurveStructure W =
      Spec.map (CommRingCat.ofHom (algebraMap R T)) :=
  WeierstrassIntegralChart.integralChartPoint_structure W 2 _ _ _

end FLT.Mazur.WeierstrassDilatation
