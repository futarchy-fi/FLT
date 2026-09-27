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


end WeierstrassCurve.Affine.FunctionField
