/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticVariableChangeSmoothness

/-!
# Variable changes on smooth point groups of possibly singular cubics

The coordinate map preserves nonsingularity and addition without an
ellipticity assumption. This permits normalization of bad special fibers.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve WeierstrassCurve.Affine

variable {F : Type*} [Field F] (W : WeierstrassCurve F) (C : VariableChange F)

/-- A variable change carries smooth affine points to smooth affine points. -/
def smoothPointChangeFun : (C • W).toAffine.Point → W.toAffine.Point
  | .zero => .zero
  | .some x y h => .some ((C.u : F) ^ 2 * x + C.r)
      ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
      ((variableChange_nonsingular W C x y).mpr h)

/-- The smooth coordinate map is injective. -/
theorem smoothPointChangeFun_injective : Function.Injective (smoothPointChangeFun W C) := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) h
  · rfl
  · cases h
  · cases h
  · change Point.some _ _ _ = Point.some _ _ _ at h
    injection h with hX hY
    have hx : x₁ = x₂ := mul_left_cancel₀ (pow_ne_zero 2 hu) (by linear_combination hX)
    exact Point.some_eq_some (C • W) hx
      (mul_left_cancel₀ (pow_ne_zero 3 hu)
        (by linear_combination hY - (C.u : F) ^ 2 * C.s * hx))

variable [DecidableEq F]

/-- The coordinate map respects the actual group law, even on a singular cubic. -/
def smoothPointChangeHom : (C • W).toAffine.Point →+ W.toAffine.Point where
  toFun := smoothPointChangeFun W C
  map_zero' := rfl
  map_add' := by
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩)
    any_goals rfl
    change smoothPointChangeFun W C (Point.some _ _ h₁ + Point.some _ _ h₂) =
      Point.some _ _ _ + Point.some _ _ _
    by_cases hxy : x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂
    · rw [Point.add_of_Y_eq hxy.1 hxy.2]
      change 0 = _
      refine (Point.add_of_Y_eq ?_ ?_).symm
      · rw [hxy.1]
      · rw [variableChange_negY, hxy.2, hxy.1]
    · rw [Point.add_some hxy, Point.add_some (variableChange_negY_ne W C hxy)]
      change Point.some _ _ _ = Point.some _ _ _
      simp only [variableChange_slope W C h₁.1 h₂.1 hxy,
        variableChange_addX, variableChange_addY]

omit [DecidableEq F] in
/-- Every smooth point has a smooth preimage under a variable change. -/
theorem smoothPointChangeFun_surjective : Function.Surjective (smoothPointChangeFun W C) := by
  classical
  intro P
  refine ⟨smoothPointChangeFun (C • W) C⁻¹
    (Point.equivOfEq (inv_smul_smul C W).symm P), ?_⟩
  cases P with
  | zero => simp only [← Point.zero_def, map_zero, smoothPointChangeFun]
  | some x y h =>
    rw [Point.equivOfEq_some]
    change Point.some _ _ _ = Point.some _ _ _
    apply Point.some_eq_some W <;>
      (simp only [VariableChange.inv_def, Units.val_inv_eq_inv_val]; field)

/-- An integral or field variable change induces an equivalence on smooth point groups. -/
noncomputable def smoothPointChangeEquiv : (C • W).toAffine.Point ≃+ W.toAffine.Point :=
  AddEquiv.ofBijective (smoothPointChangeHom W C)
    ⟨smoothPointChangeFun_injective W C, smoothPointChangeFun_surjective W C⟩

end FLT.Mazur
