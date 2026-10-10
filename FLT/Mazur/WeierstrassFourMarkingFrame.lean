/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.Data.ZMod.Basic

/-!
# Three affine points detected by a faithful four-torsion marking

The labels (1,0), (-1,0), and (0,1) give a coordinate frame over every field.
Faithfulness makes the first two ordinates distinct and the first and third
abscissas distinct. No torsion cardinality or classification of automorphisms
is assumed.
-/

@[expose] public section

open WeierstrassCurve WeierstrassCurve.Affine

namespace FLT.Mazur.WeierstrassFourMarkingFrame

variable {K : Type*} [Field K] [DecidableEq K] (W : WeierstrassCurve K)
  (φ : (ZMod 4 × ZMod 4) →+ W.toAffine.Point) (hφ : Function.Injective φ)

include hφ

/-- The first basis label is a nonzero affine point. -/
theorem first_ne_zero : φ (1, 0) ≠ 0 := by
  intro h
  have := hφ (h.trans φ.map_zero.symm)
  exact (by decide : ((1, 0) : ZMod 4 × ZMod 4) ≠ 0) this

/-- The second basis label is a nonzero affine point. -/
theorem second_ne_zero : φ (0, 1) ≠ 0 := by
  intro h
  have := hφ (h.trans φ.map_zero.symm)
  exact (by decide : ((0, 1) : ZMod 4 × ZMod 4) ≠ 0) this

/-- The first label has order four, so it is distinct from its inverse. -/
theorem first_ne_neg : φ (1, 0) ≠ -φ (1, 0) := by
  intro h
  have := hφ (h.trans (φ.map_neg (1, 0)).symm)
  exact (by decide : ((1, 0) : ZMod 4 × ZMod 4) ≠ -(1, 0)) this

/-- The two basis labels have distinct abscissas. -/
theorem first_ne_second_or_neg : φ (1, 0) ≠ φ (0, 1) ∧ φ (1, 0) ≠ -φ (0, 1) := by
  constructor
  · intro h
    exact (by decide : ((1, 0) : ZMod 4 × ZMod 4) ≠ (0, 1)) (hφ h)
  · intro h
    exact (by decide : ((1, 0) : ZMod 4 × ZMod 4) ≠ -(0, 1))
      (hφ (h.trans (φ.map_neg (0, 1)).symm))

/-- Actual coordinates of the first two labels give a nondegenerate affine frame. -/
theorem exists_frame :
    ∃ (x y z w : K) (hP : W.toAffine.Nonsingular x y)
      (hQ : W.toAffine.Nonsingular z w),
      φ (1, 0) = .some x y hP ∧ φ (0, 1) = .some z w hQ ∧
        x ≠ z ∧ y ≠ W.toAffine.negY x y := by
  have hp := first_ne_zero W φ hφ
  have hq := second_ne_zero W φ hφ
  have hn := first_ne_neg W φ hφ
  have hd := first_ne_second_or_neg W φ hφ
  cases hP : φ (1, 0) with
  | zero => exact (hp hP).elim
  | some x y hxy =>
    cases hQ : φ (0, 1) with
    | zero => exact (hq hQ).elim
    | some z w hzw =>
      refine ⟨x, y, z, w, hxy, hzw, rfl, rfl, ?_, ?_⟩
      · intro hx
        rcases Point.X_eq_iff.mp hx with h | h
        · exact hd.1 (hP.trans (h.trans hQ.symm))
        · exact hd.2 (hP.trans (h.trans (congrArg Neg.neg hQ).symm))
      · intro hy
        apply hn
        rw [hP, Point.neg_some, Point.some.injEq]
        exact ⟨rfl, hy⟩

end FLT.Mazur.WeierstrassFourMarkingFrame
