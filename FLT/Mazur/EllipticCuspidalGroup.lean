/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticCuspAddition
public import FLT.Mazur.EllipticCuspTangent
public import FLT.Mazur.EllipticSmoothPointChange

/-!
# Smooth groups of arbitrary cuspidal Weierstrass equations

Over a perfect field, Δ=c₄=0 gives an additive smooth point group. The
isomorphism uses actual variable changes and the actual affine addition.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve

variable {F : Type*} [Field F] [PerfectField F] (W : WeierstrassCurve F)

/-- A cuspidal cubic over a perfect field is a variable change of the standard cusp. -/
theorem exists_cuspCurve_variableChange (hΔ : W.Δ = 0) (hc : W.c₄ = 0) :
    ∃ C : VariableChange F, C • W = cuspCurve F := by
  obtain ⟨x, y, he, hn⟩ := exists_singular_of_discriminant_zero W hΔ
  let T : VariableChange F := ⟨1, x, 0, y⟩
  obtain ⟨h3, h4, h6⟩ := translated_singular_coefficients W he hn
  have hc' : (T • W).c₄ = 0 := by simp [T, variableChange_c₄, hc]
  obtain ⟨s, h1, h2, h3, h4, h6⟩ := exists_normalized_cusp_shear (T • W) h3 h4 h6 hc'
  refine ⟨VariableChange.mk 1 0 s 0 * T, ?_⟩
  rw [mul_smul]
  exact WeierstrassCurve.ext h1 h2 h3 h4 h6

variable [DecidableEq F]

/-- The smooth point group of a cuspidal cubic is the additive group of its perfect field. -/
noncomputable def cuspidalPointAddEquiv (hΔ : W.Δ = 0) (hc : W.c₄ = 0) :
    W.toAffine.Point ≃+ F := by
  let C := (exists_cuspCurve_variableChange W hΔ hc).choose
  have hC : C • W = cuspCurve F := (exists_cuspCurve_variableChange W hΔ hc).choose_spec
  exact (smoothPointChangeEquiv W C).symm.trans
    ((Affine.Point.equivOfEq hC).trans cuspParameterAddEquiv)

/-- Prime-to-characteristic torsion on the smooth locus of a cusp is zero. -/
theorem cuspidalPoint_torsion_eq_zero (hΔ : W.Δ = 0) (hc : W.c₄ = 0)
    (p n : ℕ) [CharP F p] (hn : ¬ p ∣ n) (P : W.toAffine.Point) (hP : n • P = 0) :
    P = 0 := by
  let e := cuspidalPointAddEquiv W hΔ hc
  apply e.injective
  rw [map_zero]
  have he : (n : F) * e P = 0 := by
    simp only [← nsmul_eq_mul, ← map_nsmul, hP, map_zero]
  exact (mul_eq_zero.mp he).resolve_left ((CharP.cast_eq_zero_iff F p n).not.mpr hn)

end FLT.Mazur
