/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSecantOriginalRelations
public import FLT.Mazur.WeierstrassProjectivePointSmooth

/-!
# Smooth secants from nonsingular original inputs

When the scale is nonzero in a source field, the original abscissas are
separated by the constructed secant denominator. Mathlib's nonsingular
addition theorem then proves smoothness of the complete original output.
This includes scale one, needed for zero-depth self-pairs.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory WeierstrassCurve
namespace FLT.Mazur.WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S F : Type u} [CommRing R] [CommRing S] [Field F]
  [Algebra R S] [Algebra R F] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (a c : Coordinate W s b3 b4 b6 →ₐ[R] S)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
  (e : DividedSecantRing W s b3 b4 b6 a c →ₐ[R] F)
/-- Classical equality is used only to state the field-valued slope comparison. -/
local instance secantFieldDecidableEq : DecidableEq F := Classical.decEq F

local notation "T" => DividedSecantRing W s b3 b4 b6 a c
local notation "j" => IsScalarTower.toAlgHom R S T
local notation "a'" => (e.comp j).comp a
local notation "c'" => (e.comp j).comp c
local notation "orig" => fromOriginal W s b3 b4 b6 h3 h4 h6
local notation "A" => (a').comp orig
local notation "C" => (c').comp orig
local notation "x₀" => WeierstrassIntegralChart.coord W 2 0
local notation "y₀" => WeierstrassIntegralChart.coord W 2 1
local notation "l" => e (dividedSecantSlope W s b3 b4 b6 a c)
local notation "WF" => (W.map (algebraMap R F)).toAffine
local notation "out" => dividedSecantOutput W s b3 b4 b6 a c h3 h4 h6
local notation "f" => dividedSecantToCurve W s b3 b4 b6 a c h3 h4 h6

/-- A nonzero scale separates the original abscissas on every secant field point. -/
theorem dividedSecantRefinement_original_x_ne (hs : algebraMap R F s ≠ 0) :
    A x₀ ≠ C x₀ := by
  apply sub_ne_zero.mp
  have hd := (dividedSecantRefinement_denominator_isUnit W s b3 b4 b6 a c e).ne_zero
  simpa only [AlgHom.comp_apply, fromOriginal_x, map_mul, AlgHom.commutes, ← mul_sub]
    using mul_ne_zero hs hd

/-- The constructed original slope is Mathlib's secant slope at a nonzero scale. -/
theorem dividedSecantRefinement_original_slope (hs : algebraMap R F s ≠ 0) :
    l = (WF).slope (A x₀) (C x₀) (A y₀) (C y₀) := by
  have hx := dividedSecantRefinement_original_x_ne W s b3 b4 b6 a c h3 h4 h6 e hs
  rw [Affine.slope_of_X_ne hx]
  apply (eq_div_iff (sub_ne_zero.mpr hx)).mpr
  exact dividedSecantRefinement_original_line W s b3 b4 b6 a c h3 h4 h6 e

/-- Smooth original inputs give a nonsingular output, without a positive-depth assumption. -/
theorem dividedSecantRefinement_nonsingular (hs : algebraMap R F s ≠ 0)
    (ha : (WF).Nonsingular (A x₀) (A y₀))
    (hc : (WF).Nonsingular (C x₀) (C y₀)) :
    (WF).Nonsingular ((e.comp out) x₀) ((e.comp out) y₀) := by
  rw [dividedSecantRefinement_original_coord, dividedSecantRefinement_original_coord]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [dividedSecantRefinement_original_slope W s b3 b4 b6 a c h3 h4 h6 e hs]
  exact Affine.nonsingular_add ha hc (fun h =>
    dividedSecantRefinement_original_x_ne W s b3 b4 b6 a c h3 h4 h6 e hs h.1)

/-- The entire secant field-point map lies in the original scheme's actual smooth open. -/
theorem dividedSecantRefinement_range_smooth (hs : algebraMap R F s ≠ 0)
    (ha : (WF).Nonsingular (A x₀) (A y₀))
    (hc : (WF).Nonsingular (C x₀) (C y₀)) :
    Set.range (Spec.map (CommRingCat.ofHom e.toRingHom) ≫ f) ⊆
      WeierstrassIntegralChart.integralSmoothOpen W := by
  let o := e.comp out
  have ho : o ∘ WeierstrassIntegralChart.coord W 2 =
      ![o x₀, o y₀, 1] := by
    funext i
    fin_cases i <;> simp
  have hn := dividedSecantRefinement_nonsingular W s b3 b4 b6 a c h3 h4 h6 e hs ha hc
  have hp := WeierstrassIntegralChart.chartFieldPoint_range_smooth W 2 o
    (by rw [ho]; exact (Projective.nonsingular_some _ _).mpr hn)
  simpa only [dividedSecantToCurve, ← Category.assoc, ← Spec.map_comp,
    o, AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom, CommRingCat.ofHom_comp] using hp

end FLT.Mazur.WeierstrassDilatation
