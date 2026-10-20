/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSecantSource
public import FLT.Mazur.EllipticNormalizedSingularity
public import FLT.Mazur.WeierstrassAffineProduct

/-!
# Opposite divided branches have an originally smooth secant output

The scale vanishes and both original inputs are the node. Distinct divided
abscissae on the two punctured tangent lines nevertheless give a nonsingular
original output. This is a new domain beyond the original-factor opens.
-/

@[expose] public noncomputable section
open WeierstrassCurve
namespace FLT.Mazur.WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- A secant crossing two punctured tangent branches avoids both forbidden slopes. -/
theorem opposite_divided_secant_nonzero {K : Type*} [Field K] {t u v l : K}
    (ht : t ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0) (hl : l * (u - v) = t * v) :
    l * (l + t) ≠ 0 := by
  have hl₀ : l ≠ 0 := by
    intro h
    exact (mul_ne_zero ht hv) (by simpa only [h, zero_mul] using hl.symm)
  have hlt : l + t ≠ 0 := by
    intro h
    apply mul_ne_zero ht hu
    linear_combination (u - v) * h - hl
  exact mul_ne_zero hl₀ hlt

universe u
variable {R S K : Type u} [CommRing R] [CommRing S] [Field K]
  [Algebra R S] [Algebra R K] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (a c : Coordinate W s b3 b4 b6 →ₐ[R] S)
  (e : DividedSecantRing W s b3 b4 b6 a c →ₐ[R] K)
local notation "T" => DividedSecantRing W s b3 b4 b6 a c
local notation "j" => IsScalarTower.toAlgHom R S T
local notation "u₁" => e (((j).comp a) (x W s b3 b4 b6))
local notation "u₂" => e (((j).comp c) (x W s b3 b4 b6))
local notation "v₁" => e (((j).comp a) (y W s b3 b4 b6))
local notation "v₂" => e (((j).comp c) (y W s b3 b4 b6))
local notation "t" => algebraMap R K W.a₁

/-- At opposite punctured branches the actual original output abscissa is nonzero. -/
theorem dividedSecantX_residue_ne_zero
    (hs : algebraMap R K s = 0) (h2 : algebraMap R K W.a₂ = 0) (ht : t ≠ 0)
    (hu : u₁ ≠ 0) (hv : u₂ ≠ 0) (hleft : v₁ = 0) (hright : v₂ = -t * u₂) :
    e (dividedSecantX W s b3 b4 b6 a c) ≠ 0 := by
  have hl := congrArg e (dividedSecantSlope_relation W s b3 b4 b6 a c)
  simp only [map_mul, map_sub, hleft, hright, zero_sub, neg_mul, neg_neg] at hl
  have hx : e (dividedSecantX W s b3 b4 b6 a c) =
      e (dividedSecantSlope W s b3 b4 b6 a c) *
        (e (dividedSecantSlope W s b3 b4 b6 a c) + t) := by
    simp only [dividedSecantX, Affine.addX, map_sub, map_add, map_mul, map_pow,
      map_a₁, map_a₂, AlgHom.commutes, hs, h2, zero_mul, sub_zero]
    ring
  rw [hx]
  exact opposite_divided_secant_nonzero ht hu hv hl

/-- The original cubic output is nonsingular even though both original inputs are the node. -/
theorem dividedSecantOutput_residue_nonsingular
    (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
    (hs : algebraMap R K s = 0) (h2 : algebraMap R K W.a₂ = 0) (ht : t ≠ 0)
    (hu : u₁ ≠ 0) (hv : u₂ ≠ 0) (hleft : v₁ = 0) (hright : v₂ = -t * u₂) :
    (W.map (algebraMap R K)).toAffine.Nonsingular
      (e (dividedSecantOutput W s b3 b4 b6 a c h3 h4 h6
        (WeierstrassIntegralChart.coord W 2 0)))
      (e (dividedSecantOutput W s b3 b4 b6 a c h3 h4 h6
        (WeierstrassIntegralChart.coord W 2 1))) := by
  apply (normalized_nonsingular_iff (W.map (algebraMap R K))
    (by simp only [map_a₃, h3, map_mul, hs, zero_mul])
    (by simp only [map_a₄, h4, map_mul, hs, zero_mul])
    (by simp only [map_a₆, h6, map_mul, map_pow, hs, zero_pow (by decide : 2 ≠ 0), zero_mul])
    (WeierstrassIntegralChart.affine_equation_of_hom W
      (e.comp (dividedSecantOutput W s b3 b4 b6 a c h3 h4 h6)))).mpr
  intro h
  apply dividedSecantX_residue_ne_zero W s b3 b4 b6 a c e hs h2 ht hu hv hleft hright
  simpa only [AlgHom.comp_apply, dividedSecantOutput, WeierstrassIntegralChart.evaluation_coord,
    Matrix.cons_val_zero] using h.1

end FLT.Mazur.WeierstrassDilatation
