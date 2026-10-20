/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentRelations
public import FLT.Mazur.WeierstrassOrdinaryChartSpecialization

/-!
# Divided tangent comparison on arbitrary affine refinements

The ordinary comparison survives every further algebra map from the tangent
source on which the original scale remains regular. Thus affine refinements
of scheme overlaps can use the formula without identifying their ring with
the universal localization. Only agreement of the input maps is assumed.
-/

@[expose] public noncomputable section
open WeierstrassCurve
namespace FLT.Mazur.WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S B : Type u} [CommRing R] [CommRing S] [CommRing B]
  [Algebra R S] [Algebra R B] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (a c : Coordinate W s b3 b4 b6 →ₐ[R] S)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
  (e : DividedTangentRing W s b3 b4 b6 a c →ₐ[R] B)
local notation "T" => DividedTangentRing W s b3 b4 b6 a c
local notation "j" => IsScalarTower.toAlgHom R S T
local notation "a'" => (e.comp j).comp a
local notation "c'" => (e.comp j).comp c
local notation "orig" => fromOriginal W s b3 b4 b6 h3 h4 h6
local notation "l" => dividedTangentSlope W s b3 b4 b6 a c
variable (b : Bool)
  (f : WeierstrassIntegralChart.additionChartRing W
    (WeierstrassIntegralChart.ordinaryIndex b) →ₐ[R] B)
  (ha : f.comp (WeierstrassIntegralChart.ordinaryInputLeft W b) =
    ((e.comp (IsScalarTower.toAlgHom R S (DividedTangentRing W s b3 b4 b6 a c))).comp a).comp
      (fromOriginal W s b3 b4 b6 h3 h4 h6))
  (hc : f.comp (WeierstrassIntegralChart.ordinaryInputRight W b) =
    ((e.comp (IsScalarTower.toAlgHom R S (DividedTangentRing W s b3 b4 b6 a c))).comp c).comp
      (fromOriginal W s b3 b4 b6 h3 h4 h6))
  (hs : IsRegular (algebraMap R B s))

include ha hc hs in
/-- Any regular affine refinement identifies the ordinary and divided tangent slopes. -/
theorem dividedTangentRefinement_slope :
    f (WeierstrassIntegralChart.ordinaryChartSlope W b) = e l := by
  have hleft (z) : f (WeierstrassIntegralChart.ordinaryInputLeft W b z) = a' (orig z) :=
    DFunLike.congr_fun ha z
  have hright (z) : f (WeierstrassIntegralChart.ordinaryInputRight W b z) = c' (orig z) :=
    DFunLike.congr_fun hc z
  have he := WeierstrassIntegralChart.ordinarySpecialization_cubic W b f
  dsimp only at he
  simp only [hleft, hright, fromOriginal_x, fromOriginal_y, map_mul, AlgHom.commutes,
    map_a₁, map_a₂, map_a₃, map_a₄, h3, h4] at he
  have hd : f (WeierstrassIntegralChart.ordinaryChartSlope W b) *
      (a' (y W s b3 b4 b6) + c' (y W s b3 b4 b6) +
        algebraMap R B W.a₁ * c' (x W s b3 b4 b6) + algebraMap R B b3) =
      algebraMap R B s * (a' (x W s b3 b4 b6) ^ 2 +
        a' (x W s b3 b4 b6) * c' (x W s b3 b4 b6) + c' (x W s b3 b4 b6) ^ 2) +
      algebraMap R B W.a₂ * (a' (x W s b3 b4 b6) + c' (x W s b3 b4 b6)) +
      algebraMap R B b4 - algebraMap R B W.a₁ * a' (y W s b3 b4 b6) := by
    apply hs.left
    linear_combination he
  apply (dividedTangentRefinement_denominator_isUnit W s b3 b4 b6 a c e).mul_left_inj.mp
  exact hd.trans (dividedTangentRefinement_chord W s b3 b4 b6 a c e).symm

include ha hc hs in
/-- The actual output algebra maps agree on every regular affine refinement of an overlap. -/
theorem dividedTangentRefinement_output :
    e.comp (dividedTangentOutput W s b3 b4 b6 a c h3 h4 h6) =
      f.comp (WeierstrassIntegralChart.ordinaryChartAddition W b) := by
  have hleft (z) : f (WeierstrassIntegralChart.ordinaryInputLeft W b z) = a' (orig z) :=
    DFunLike.congr_fun ha z
  have hright (z) : f (WeierstrassIntegralChart.ordinaryInputRight W b z) = c' (orig z) :=
    DFunLike.congr_fun hc z
  apply WeierstrassIntegralChart.hom_ext
  intro i
  rw [AlgHom.comp_apply, AlgHom.comp_apply,
    WeierstrassIntegralChart.ordinarySpecialization_coord]
  simp only [hleft, hright, fromOriginal_x, fromOriginal_y, map_mul, AlgHom.commutes,
    dividedTangentRefinement_slope W s b3 b4 b6 a c h3 h4 h6 e b f ha hc hs]
  rw [dividedTangentOutput, WeierstrassIntegralChart.evaluation_coord]
  fin_cases i <;>
    simp [dividedTangentX, dividedTangentY, Affine.addX, Affine.addY,
      Affine.negY, Affine.negAddY, AlgHom.commutes]

end FLT.Mazur.WeierstrassDilatation
