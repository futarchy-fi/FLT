/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSplitNodeAddition

/-!
# The units group of a normalized split node

The parameter r/(r+a), with value one at infinity, gives an isomorphism
from the actual smooth point group to the units of the ground field.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve

variable {F : Type*} [Field F] {a : F}

/-- For a genuine node, only infinity has multiplicative parameter one. -/
theorem splitNodeParameter_eq_one_iff (ha : a ≠ 0) (P : (splitNodeCurve a).toAffine.Point) :
    splitNodeParameter a P = 1 ↔ P = 0 := by
  cases P with
  | zero => simp [splitNodeParameter, Affine.Point.zero_def]
  | some x y h =>
    have hra := (splitNodeCurve_slope_ne h).2
    have hn : y / x / (y / x + a) ≠ 1 := by
      intro he
      have he' := (div_eq_one_iff_eq hra).mp he
      apply ha
      linear_combination -he'
    simp only [splitNodeParameter, hn, Affine.Point.zero_def, reduceCtorEq]

/-- For a genuine node, the parameter distinguishes all smooth points. -/
theorem splitNodeParameter_injective (ha : a ≠ 0) :
    Function.Injective (splitNodeParameter a) := by
  intro P Q he
  cases P with
  | zero =>
    exact ((splitNodeParameter_eq_one_iff ha Q).mp he.symm).symm
  | some x y h =>
    cases Q with
    | zero => exact (splitNodeParameter_eq_one_iff ha _).mp he
    | some x' y' h' =>
      have hra := (splitNodeCurve_slope_ne h).2
      have hsa := (splitNodeCurve_slope_ne h').2
      have he' := (div_eq_div_iff hra hsa).mp he
      have hrs : y / x = y' / x' := by
        apply sub_eq_zero.mp
        apply (mul_eq_zero.mp (show a * (y / x - y' / x') = 0 by
          linear_combination he')).resolve_left ha
      obtain ⟨ex, ey⟩ := splitNodeCurve_coordinates_slope h
      obtain ⟨ex', ey'⟩ := splitNodeCurve_coordinates_slope h'
      apply (Affine.Point.some.injEq _ _ _ _ _ _).mpr
      exact ⟨by rw [← ex, ← ex', hrs], by rw [← ey, ← ey', hrs]⟩

/-- Every unit occurs as the parameter of a smooth point of a genuine split node. -/
theorem splitNodeParameterUnit_surjective (ha : a ≠ 0) :
    Function.Surjective (splitNodeParameterUnit a) := by
  intro u
  by_cases hu : (u : F) = 1
  · refine ⟨0, Units.ext ?_⟩
    exact hu.symm
  · let r : F := a * (u : F) / (1 - (u : F))
    have hd : 1 - (u : F) ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
    have hr : r ≠ 0 := div_ne_zero (mul_ne_zero ha u.ne_zero) hd
    have he : r + a = a / (1 - (u : F)) := by dsimp [r]; field_simp; ring
    have hra : r + a ≠ 0 := by rw [he]; exact div_ne_zero ha hd
    refine ⟨.some _ _ (splitNodeCurve_nonsingular_param hr hra), Units.ext ?_⟩
    simp only [splitNodeParameterUnit, Units.val_mk0]
    rw [splitNodeParameter_param hr hra, he]
    dsimp [r]
    field_simp

variable [DecidableEq F]

/-- The smooth split-node parameter as a homomorphism to field units. -/
noncomputable def splitNodeParameterHom (a : F) :
    (splitNodeCurve a).toAffine.Point →+ Additive Fˣ where
  toFun := fun P => Additive.ofMul (splitNodeParameterUnit a P)
  map_zero' := Units.ext rfl
  map_add' := fun P Q => Units.ext (splitNodeParameter_add a P Q)

/-- The actual smooth point group of a split node is the multiplicative group of the field. -/
noncomputable def splitNodeParameterAddEquiv (ha : a ≠ 0) :
    (splitNodeCurve a).toAffine.Point ≃+ Additive Fˣ :=
  AddEquiv.ofBijective (splitNodeParameterHom a)
    ⟨fun _ _ he => splitNodeParameter_injective ha (congrArg (fun u : Fˣ => (u : F)) he),
      splitNodeParameterUnit_surjective ha⟩

end FLT.Mazur
