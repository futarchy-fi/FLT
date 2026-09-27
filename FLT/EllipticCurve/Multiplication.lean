/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.NTorsionFinite
public import FLT.EllipticCurve.Translation

/-!
# Multiplication pullbacks on the function field

A positive multiple of the generic point is nonconstant. Over an
algebraically closed ground field its x-coordinate is therefore
transcendental, allowing evaluation on the function field.
-/

@[expose] public section

open Polynomial
open scoped WeierstrassCurve.Affine
namespace WeierstrassCurve.Affine.FunctionField
variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve.Affine F)
variable [W.IsElliptic] [IsAlgClosed F]

/-- An elliptic curve over an algebraically closed field has a point not killed
by any prescribed positive integer. -/
theorem exists_nsmul_ne_zero {n : ℕ} (hn : n ≠ 0) : ∃ Q : W.Point, n • Q ≠ 0 := by
  have hp := W.ΨSq_ne_zero_of_isElliptic (Int.natCast_ne_zero.mpr hn)
  obtain ⟨x, hx⟩ := (Polynomial.finite_setOfPred_isRoot hp).exists_notMem
  obtain ⟨y, hy⟩ := W.exists_equation x
  have h : W.Nonsingular x y := W.equation_iff_nonsingular.mp hy
  exact ⟨Point.some x y h, fun hz => hx (W.isRoot_ΨSq_of_nsmul_eq_zero h n hz)⟩

set_option backward.isDefEq.respectTransparency false in
/-- A positive multiple of the generic point is nonconstant. Translating a
constant multiple would force every ground-field point to be n-torsion. -/
theorem nsmul_genericPoint_not_mem_range {n : ℕ} (hn : n ≠ 0) :
    n • genericPoint W ∉
      (Point.map (W' := W) (Algebra.ofId F W.FunctionField)).range := by
  rintro ⟨R, hR⟩
  obtain ⟨Q, hQ⟩ := exists_nsmul_ne_zero W hn
  have he := congrArg (Point.map (W' := W) (translationPullback W Q)) hR
  rw [map_basePoint, map_nsmul, translationPullback_genericPoint, nsmul_add, ← hR] at he
  have hz : n • Point.map (W' := W) (Algebra.ofId F W.FunctionField) Q = 0 := by
    exact (add_eq_left.mp he.symm)
  apply hQ
  apply Point.map_injective (W' := W) (Algebra.ofId F W.FunctionField)
  simpa only [map_nsmul, map_zero] using hz


section

omit [DecidableEq F]

/-- A positive multiple of the generic point has affine coordinates with
transcendental x-coordinate. -/
theorem exists_multiplied_generic (n : ℕ) (hn : n ≠ 0) :
    ∃ x y, ∃ h : (W⁄W.FunctionField).Nonsingular x y,
      Point.some x y h = n • genericPoint W ∧ Transcendental F x := by
  classical
  have hnc := nsmul_genericPoint_not_mem_range W hn
  cases hp : n • genericPoint W with
  | zero => exact False.elim (hnc (hp ▸ AddSubgroup.zero_mem _))
  | some x y h =>
    refine ⟨x, y, h, rfl, ?_⟩
    intro hx
    apply hnc
    rw [hp]
    exact point_mem_range_of_isAlgebraic_x h hx

/-- The x-coordinate of the generic point multiplied by n. -/
noncomputable def multipliedX (n : ℕ) (hn : n ≠ 0) : W.FunctionField :=
  (exists_multiplied_generic W n hn).choose

/-- The y-coordinate of the generic point multiplied by n. -/
noncomputable def multipliedY (n : ℕ) (hn : n ≠ 0) : W.FunctionField :=
  (exists_multiplied_generic W n hn).choose_spec.choose

/-- The multiplied generic coordinates form a nonsingular point. -/
theorem multiplied_nonsingular (n : ℕ) (hn : n ≠ 0) :
    (W⁄W.FunctionField).Nonsingular (multipliedX W n hn) (multipliedY W n hn) :=
  (exists_multiplied_generic W n hn).choose_spec.choose_spec.choose

/-- The chosen multiplied coordinates represent n times the generic point. -/
theorem multiplied_point (n : ℕ) (hn : n ≠ 0) :
    Point.some (multipliedX W n hn) (multipliedY W n hn) (multiplied_nonsingular W n hn) =
      n • genericPoint W :=
  (exists_multiplied_generic W n hn).choose_spec.choose_spec.choose_spec.1

/-- The x-coordinate of a positive multiple of the generic point is transcendental. -/
theorem multipliedX_transcendental (n : ℕ) (hn : n ≠ 0) :
    Transcendental F (multipliedX W n hn) :=
  (exists_multiplied_generic W n hn).choose_spec.choose_spec.choose_spec.2

/-- Pullback of rational functions by multiplication by a positive integer. -/
noncomputable def nsmulPullback (n : ℕ) (hn : n ≠ 0) : W.FunctionField →ₐ[F] W.FunctionField :=
  CoordinateRing.evalFunctionField (multiplied_nonsingular W n hn).1
    (multipliedX_transcendental W n hn)

set_option backward.isDefEq.respectTransparency false in
/-- Multiplication pullback sends the generic x-coordinate to the multiplied coordinate. -/
theorem nsmulPullback_genericX (n : ℕ) (hn : n ≠ 0) :
    nsmulPullback W n hn (genericX W) = multipliedX W n hn := by
  rw [nsmulPullback, genericX, CoordinateRing.evalFunctionField_algebraMap,
    CoordinateRing.evalAt_polynomial, aeval_X]

set_option backward.isDefEq.respectTransparency false in
/-- Multiplication pullback sends the generic y-coordinate to the multiplied coordinate. -/
theorem nsmulPullback_genericY (n : ℕ) (hn : n ≠ 0) :
    nsmulPullback W n hn (genericY W) = multipliedY W n hn := by
  rw [nsmulPullback, genericY, CoordinateRing.evalFunctionField_algebraMap,
    CoordinateRing.evalAt_Y]

/-- Multiplication pullback sends the generic point to its n-fold multiple. -/
theorem nsmulPullback_genericPoint (n : ℕ) (hn : n ≠ 0) :
    Point.map (W' := W) (nsmulPullback W n hn) (genericPoint W) = n • genericPoint W := by
  rw [genericPoint, Point.map_some]
  simp only [nsmulPullback_genericX, nsmulPullback_genericY]
  exact multiplied_point W n hn

set_option backward.isDefEq.respectTransparency false in
/-- Pullback by multiplication by one is the identity. -/
theorem nsmulPullback_one : nsmulPullback W 1 one_ne_zero = AlgHom.id F W.FunctionField := by
  apply algHom_ext_of_genericPoint W
  rw [nsmulPullback_genericPoint, one_smul]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Composing multiplication pullbacks multiplies their indices. -/
theorem nsmulPullback_mul (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) :
    (nsmulPullback W m hm).comp (nsmulPullback W n hn) =
      nsmulPullback W (m * n) (mul_ne_zero hm hn) := by
  apply algHom_ext_of_genericPoint W
  rw [← Point.map_map, nsmulPullback_genericPoint, map_nsmul,
    nsmulPullback_genericPoint, nsmulPullback_genericPoint, smul_smul, Nat.mul_comm]

end

set_option backward.isDefEq.respectTransparency false in
/-- Translating a multiplication pullback translates its source by n times the point. -/
theorem translation_nsmulPullback (n : ℕ) (hn : n ≠ 0) (Q : W.Point) :
    (translationPullback W Q).comp (nsmulPullback W n hn) =
      (nsmulPullback W n hn).comp (translationPullback W (n • Q)) := by
  apply algHom_ext_of_genericPoint W
  rw [← Point.map_map, ← Point.map_map, nsmulPullback_genericPoint,
    translationPullback_genericPoint, map_add, map_nsmul,
    translationPullback_genericPoint, nsmulPullback_genericPoint, map_basePoint,
    nsmul_add, map_nsmul]

set_option backward.isDefEq.respectTransparency false in
/-- Pullbacks by multiplication by n are invariant under n-torsion translations. -/
theorem translation_nsmulPullback_of_torsion (n : ℕ) (hn : n ≠ 0) (Q : W.Point)
    (hQ : n • Q = 0) :
    (translationPullback W Q).comp (nsmulPullback W n hn) = nsmulPullback W n hn := by
  rw [translation_nsmulPullback, hQ, translationPullback_zero, AlgHom.comp_id]

/-- If the nth power of a nonzero function is pulled back by multiplication by n,
translation by n-torsion changes that function by a constant nth root of unity. -/
theorem exists_translation_ratio_of_pow_eq_pullback (n : ℕ) (hn : n ≠ 0)
    (Q : W.Point) (hQ : n • Q = 0) {f g : W.FunctionField} (hg0 : g ≠ 0)
    (hg : g ^ n = nsmulPullback W n hn f) :
    ∃ c : F, c ≠ 0 ∧ c ^ n = 1 ∧
      translationPullback W Q g / g = algebraMap F W.FunctionField c := by
  let r := translationPullback W Q g / g
  have hr : r ^ n = 1 := by
    dsimp only [r]
    rw [div_pow, ← map_pow, hg]
    have he := congrArg (fun φ : W.FunctionField →ₐ[F] W.FunctionField => φ f)
      (translation_nsmulPullback_of_torsion W n hn Q hQ)
    change translationPullback W Q (nsmulPullback W n hn f) = nsmulPullback W n hn f at he
    rw [he]
    exact div_self (hg ▸ pow_ne_zero n hg0)
  have ha : IsAlgebraic F r :=
    ⟨X ^ n - C 1, X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero hn) 1, by simp [hr]⟩
  obtain ⟨c, hc⟩ := ha.exists_algebraMap_eq
  have hcn : c ^ n = 1 := by
    apply (algebraMap F W.FunctionField).injective
    rw [map_pow, hc, hr, map_one]
  refine ⟨c, ?_, hcn, hc.symm⟩
  intro hz
  rw [hz, zero_pow hn] at hcn
  exact zero_ne_one hcn

end WeierstrassCurve.Affine.FunctionField
