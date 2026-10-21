/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentOriginalRelations
public import FLT.Mazur.WeierstrassProjectivePointSmooth

/-!
# Smooth tangents from nonsingular original inputs

When the scale is nonzero in a source field, the original ordinate sum is
nonzero. The line and chord relations identify the actual slope, including
on the diagonal. Nonsingular addition then proves smoothness of the output.
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
  (e : DividedTangentRing W s b3 b4 b6 a c →ₐ[R] F)
/-- Classical equality is used only to state the field-valued slope comparison. -/
local instance tangentFieldDecidableEq : DecidableEq F := Classical.decEq F

local notation "T" => DividedTangentRing W s b3 b4 b6 a c
local notation "j" => IsScalarTower.toAlgHom R S T
local notation "a'" => (e.comp j).comp a
local notation "c'" => (e.comp j).comp c
local notation "orig" => fromOriginal W s b3 b4 b6 h3 h4 h6
local notation "A" => (a').comp orig
local notation "C" => (c').comp orig
local notation "x₀" => WeierstrassIntegralChart.coord W 2 0
local notation "y₀" => WeierstrassIntegralChart.coord W 2 1
local notation "l" => e (dividedTangentSlope W s b3 b4 b6 a c)
local notation "WF" => (W.map (algebraMap R F)).toAffine
local notation "out" => dividedTangentOutput W s b3 b4 b6 a c h3 h4 h6
local notation "f" => dividedTangentToCurve W s b3 b4 b6 a c h3 h4 h6

/-- The original ordinate sum is nonzero whenever the scale is nonzero. -/
theorem dividedTangentRefinement_original_denominator (hs : algebraMap R F s ≠ 0) :
    A y₀ + C y₀ + algebraMap R F W.a₁ * C x₀ + algebraMap R F W.a₃ ≠ 0 := by
  have hd := (dividedTangentRefinement_denominator_isUnit W s b3 b4 b6 a c e).ne_zero
  convert mul_ne_zero hs hd using 1
  simp only [AlgHom.comp_apply, fromOriginal_x, fromOriginal_y, h3, map_mul,
    AlgHom.commutes]
  ring

/-- The tangent source excludes inverse pairs at every nonzero scale. -/
theorem dividedTangentRefinement_original_y_ne (hs : algebraMap R F s ≠ 0) :
    A y₀ ≠ (WF).negY (C x₀) (C y₀) := by
  intro h
  apply dividedTangentRefinement_original_denominator W s b3 b4 b6 a c h3 h4 h6 e hs
  simp only [Affine.negY, map_a₁, map_a₃] at h
  linear_combination h

/-- The constructed slope is Mathlib's slope, including coincident inputs. -/
theorem dividedTangentRefinement_original_slope (hs : algebraMap R F s ≠ 0) :
    l = (WF).slope (A x₀) (C x₀) (A y₀) (C y₀) := by
  have hy := dividedTangentRefinement_original_y_ne W s b3 b4 b6 a c h3 h4 h6 e hs
  have hl := dividedTangentRefinement_original_line W s b3 b4 b6 a c h3 h4 h6 e
  by_cases hx : A x₀ = C x₀
  · have he : A y₀ = C y₀ := by
      apply sub_eq_zero.mp
      simpa only [hx, sub_self, mul_zero] using hl.symm
    rw [Affine.slope_of_Y_ne hx hy]
    apply (eq_div_iff (sub_ne_zero.mpr (by simpa only [hx, he] using hy))).mpr
    have hc := dividedTangentRefinement_original_chord W s b3 b4 b6 a c h3 h4 h6 e
    simp only [Affine.negY, map_a₁, map_a₂, map_a₃, map_a₄]
    rw [← hx, ← he] at hc
    linear_combination hc
  · rw [Affine.slope_of_X_ne hx]
    exact (eq_div_iff (sub_ne_zero.mpr hx)).mpr hl

/-- Smooth original inputs give a nonsingular output, without a positive-depth assumption. -/
theorem dividedTangentRefinement_nonsingular (hs : algebraMap R F s ≠ 0)
    (ha : (WF).Nonsingular (A x₀) (A y₀))
    (hc : (WF).Nonsingular (C x₀) (C y₀)) :
    (WF).Nonsingular ((e.comp out) x₀) ((e.comp out) y₀) := by
  rw [dividedTangentRefinement_original_coord, dividedTangentRefinement_original_coord]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [dividedTangentRefinement_original_slope W s b3 b4 b6 a c h3 h4 h6 e hs]
  exact Affine.nonsingular_add ha hc (fun h =>
    dividedTangentRefinement_original_y_ne W s b3 b4 b6 a c h3 h4 h6 e hs h.2)

/-- The entire tangent field-point map lies in the original scheme's actual smooth open. -/
theorem dividedTangentRefinement_range_smooth (hs : algebraMap R F s ≠ 0)
    (ha : (WF).Nonsingular (A x₀) (A y₀))
    (hc : (WF).Nonsingular (C x₀) (C y₀)) :
    Set.range (Spec.map (CommRingCat.ofHom e.toRingHom) ≫ f) ⊆
      WeierstrassIntegralChart.integralSmoothOpen W := by
  let o := e.comp out
  have ho : o ∘ WeierstrassIntegralChart.coord W 2 =
      ![o x₀, o y₀, 1] := by
    funext i
    fin_cases i <;> simp
  have hn := dividedTangentRefinement_nonsingular W s b3 b4 b6 a c h3 h4 h6 e hs ha hc
  have hp := WeierstrassIntegralChart.chartFieldPoint_range_smooth W 2 o
    (by rw [ho]; exact (Projective.nonsingular_some _ _).mpr hn)
  simpa only [dividedTangentToCurve, ← Category.assoc, ← Spec.map_comp,
    o, AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom, CommRingCat.ofHom_comp] using hp

end FLT.Mazur.WeierstrassDilatation
