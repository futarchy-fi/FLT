/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.PointReduction

/-!
# Addition on the integral affine chart

Coordinate reduction commutes with negation. For integral affine points whose
reductions are not opposites, it also commutes with addition. A second slope
formula handles pairs whose x-coordinates become equal in the residue field.
-/

@[expose] public section

open IsLocalRing
namespace WeierstrassCurve
variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  [(W.map (residue A)).IsElliptic]

/-- The slope through two points, using a denominator that remains nonzero when
their x-coordinates coincide and their y-coordinates are not opposite. -/
theorem Affine.slope_eq_of_Y_ne {F : Type*} [Field F] [DecidableEq F]
    (E : WeierstrassCurve F) {x₁ y₁ x₂ y₂ : F}
    (h₁ : E.toAffine.Equation x₁ y₁) (h₂ : E.toAffine.Equation x₂ y₂)
    (hy : y₁ ≠ E.toAffine.negY x₂ y₂) :
    E.toAffine.slope x₁ x₂ y₁ y₂ =
      (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + E.a₂ * (x₁ + x₂) + E.a₄ - E.a₁ * y₁) /
        (y₁ + y₂ + E.a₁ * x₂ + E.a₃) := by
  have hd : y₁ + y₂ + E.a₁ * x₂ + E.a₃ ≠ 0 := by
    intro he
    apply hy
    simp only [negY]
    linear_combination he
  by_cases hx : x₁ = x₂
  · have hy' : y₁ = y₂ := (Y_eq_of_X_eq h₁ h₂ hx).resolve_right hy
    rw [slope_of_Y_ne hx hy, hx, hy']
    simp only [negY]
    congr 1 <;> ring
  · rw [slope_of_X_ne hx, div_eq_div_iff (sub_ne_zero.mpr hx) hd]
    rw [equation_iff] at h₁ h₂
    linear_combination h₁ - h₂

/-- Coordinate reduction commutes with negation, including outside the integral chart. -/
theorem reducePoint_neg (P : (W.map (algebraMap A K)).toAffine.Point) :
    W.reducePoint A (-P) = -W.reducePoint A P := by
  classical
  cases P with
  | zero => rfl
  | some x y h =>
    have hi : x ∈ A ∧ (W.map (algebraMap A K)).toAffine.negY x y ∈ A ↔ x ∈ A ∧ y ∈ A := by
      constructor
      · rintro ⟨hx, hy⟩
        refine ⟨hx, ?_⟩
        have hh := A.toSubring.sub_mem (A.toSubring.sub_mem (A.toSubring.neg_mem hy)
          (A.toSubring.mul_mem W.a₁.property hx)) W.a₃.property
        have he : -(W.map (algebraMap A K)).toAffine.negY x y -
            (W.a₁ : K) * x - W.a₃ = y := by
          simp only [Affine.negY, map_a₁, map_a₃, ValuationSubring.algebraMap_apply]
          ring
        exact he ▸ hh
      · rintro ⟨hx, hy⟩
        exact ⟨hx, A.toSubring.sub_mem (A.toSubring.sub_mem (A.toSubring.neg_mem hy)
          (A.toSubring.mul_mem W.a₁.property hx)) W.a₃.property⟩
    by_cases hxy : x ∈ A ∧ y ∈ A
    · simp only [Affine.Point.neg_some, reducePoint, dite_eq_left hxy, dite_eq_left (hi.mpr hxy)]
      congr 1
    · simp only [Affine.Point.neg_some, reducePoint, dite_eq_right hxy,
        dite_eq_right (mt hi.mp hxy)]
      rfl

/-- Coefficientwise reduction with coordinates written using the algebra map. -/
private theorem reducePoint_some_map (x y : A)
    (h : (W.map (algebraMap A K)).toAffine.Nonsingular (algebraMap A K x) (algebraMap A K y)) :
    W.reducePoint A (.some _ _ h) = .some (residue A x) (residue A y)
      (W.nonsingular_residue_of_nonsingular A h) := W.reducePoint_some A x y h

/-- An integral slope that reduces to the special-fiber slope gives compatible addition. -/
theorem reducePoint_add_of_integral_slope [DecidableEq K] [DecidableEq (ResidueField A)]
    (x₁ y₁ x₂ y₂ l : A)
    (h₁ : (W.map (algebraMap A K)).toAffine.Nonsingular (algebraMap A K x₁) (algebraMap A K y₁))
    (h₂ : (W.map (algebraMap A K)).toAffine.Nonsingular (algebraMap A K x₂) (algebraMap A K y₂))
    (hxy : ¬ ((algebraMap A K x₁) = algebraMap A K x₂ ∧ (algebraMap A K y₁) =
      (W.map (algebraMap A K)).toAffine.negY (algebraMap A K x₂) (algebraMap A K y₂)))
    (hrxy : ¬ (residue A x₁ = residue A x₂ ∧ residue A y₁ =
      (W.map (residue A)).toAffine.negY (residue A x₂) (residue A y₂)))
    (hl : (W.map (algebraMap A K)).toAffine.slope (algebraMap A K x₁) (algebraMap A K x₂)
      (algebraMap A K y₁) (algebraMap A K y₂) = algebraMap A K l)
    (hrl : (W.map (residue A)).toAffine.slope (residue A x₁) (residue A x₂)
      (residue A y₁) (residue A y₂) = residue A l) :
    W.reducePoint A (.some _ _ h₁ + .some _ _ h₂) =
      W.reducePoint A (.some _ _ h₁) + W.reducePoint A (.some _ _ h₂) := by
  rw [Affine.Point.add_some hxy, reducePoint_some_map, reducePoint_some_map,
    Affine.Point.add_some hrxy]
  simp only [hl, hrl]
  have hx := W.toAffine.map_addX (algebraMap A K) x₁ x₂ l
  have hy := W.toAffine.map_addY (algebraMap A K) x₁ y₁ x₂ l
  change (W.map (algebraMap A K)).toAffine.addX _ _ _ = _ at hx
  change (W.map (algebraMap A K)).toAffine.addY _ _ _ _ = _ at hy
  simp only [hx, hy, reducePoint_some_map]
  congr 1
/-- Reduction preserves addition when the reduced x-coordinates are distinct. -/
theorem reducePoint_add_of_residue_x_ne [DecidableEq K] [DecidableEq (ResidueField A)]
    (x₁ y₁ x₂ y₂ : A)
    (h₁ : (W.map (algebraMap A K)).toAffine.Nonsingular (algebraMap A K x₁) (algebraMap A K y₁))
    (h₂ : (W.map (algebraMap A K)).toAffine.Nonsingular (algebraMap A K x₂) (algebraMap A K y₂))
    (hx : residue A x₁ ≠ residue A x₂) :
    W.reducePoint A (.some _ _ h₁ + .some _ _ h₂) =
      W.reducePoint A (.some _ _ h₁) + W.reducePoint A (.some _ _ h₂) := by
  have hx' : algebraMap A K x₁ ≠ algebraMap A K x₂ :=
    fun he => hx (congrArg (residue A) ((IsFractionRing.injective A K) he))
  have hu : IsUnit (x₁ - x₂) := (residue_ne_zero_iff_isUnit _).mp (by
    simpa only [map_sub, sub_ne_zero] using hx)
  let l : A := (y₁ - y₂) * ↑hu.unit⁻¹
  apply W.reducePoint_add_of_integral_slope A x₁ y₁ x₂ y₂ l h₁ h₂
    (fun h => hx' h.1) (fun h => hx h.1)
  · rw [Affine.slope_of_X_ne hx']
    simp only [l, map_mul, map_sub, map_units_inv, hu.unit_spec, div_eq_mul_inv]
  · rw [Affine.slope_of_X_ne hx]
    simp only [l, map_mul, map_sub, map_units_inv, hu.unit_spec, div_eq_mul_inv]
/-- Reduction preserves addition when the reduced y-coordinates are not opposite. -/
theorem reducePoint_add_of_residue_y_ne [DecidableEq K] [DecidableEq (ResidueField A)]
    (x₁ y₁ x₂ y₂ : A)
    (h₁ : (W.map (algebraMap A K)).toAffine.Nonsingular (algebraMap A K x₁) (algebraMap A K y₁))
    (h₂ : (W.map (algebraMap A K)).toAffine.Nonsingular (algebraMap A K x₂) (algebraMap A K y₂))
    (hy : residue A y₁ ≠
      (W.map (residue A)).toAffine.negY (residue A x₂) (residue A y₂)) :
    W.reducePoint A (.some _ _ h₁ + .some _ _ h₂) =
      W.reducePoint A (.some _ _ h₁) + W.reducePoint A (.some _ _ h₂) := by
  have hy' : algebraMap A K y₁ ≠ (W.map (algebraMap A K)).toAffine.negY
      (algebraMap A K x₂) (algebraMap A K y₂) := by
    rw [W.toAffine.map_negY]
    intro he
    apply hy
    rw [W.toAffine.map_negY]
    exact congrArg (residue A) ((IsFractionRing.injective A K) he)
  let d := y₁ + y₂ + W.a₁ * x₂ + W.a₃
  have hu : IsUnit d := (residue_ne_zero_iff_isUnit _).mp (by
    intro he
    apply hy
    simp only [d, map_add, map_mul] at he
    simp only [Affine.negY, map_a₁, map_a₃]
    linear_combination he)
  let l := (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₁) *
    (↑hu.unit⁻¹ : A)
  apply W.reducePoint_add_of_integral_slope A x₁ y₁ x₂ y₂ l h₁ h₂
    (fun h => hy' h.2) (fun h => hy h.2)
  · rw [Affine.slope_eq_of_Y_ne _ h₁.1 h₂.1 hy']
    simp only [l, d, map_mul, map_sub, map_add, map_pow, map_units_inv,
      hu.unit_spec, map_a₁, map_a₂, map_a₄, map_a₃, div_eq_mul_inv]
  · rw [Affine.slope_eq_of_Y_ne _ (W.nonsingular_residue_of_nonsingular A h₁).1
      (W.nonsingular_residue_of_nonsingular A h₂).1 hy]
    simp only [l, d, map_mul, map_sub, map_add, map_pow, map_units_inv,
      hu.unit_spec, map_a₁, map_a₂, map_a₄, map_a₃, div_eq_mul_inv]
/-- Reduction preserves addition of integral affine points whose reductions are not opposites. -/
theorem reducePoint_add_of_residue_ne_neg [DecidableEq K] [DecidableEq (ResidueField A)]
    (x₁ y₁ x₂ y₂ : A)
    (h₁ : (W.map (algebraMap A K)).toAffine.Nonsingular (algebraMap A K x₁) (algebraMap A K y₁))
    (h₂ : (W.map (algebraMap A K)).toAffine.Nonsingular (algebraMap A K x₂) (algebraMap A K y₂))
    (hred : W.reducePoint A (.some _ _ h₁) ≠ -W.reducePoint A (.some _ _ h₂)) :
    W.reducePoint A (.some _ _ h₁ + .some _ _ h₂) =
      W.reducePoint A (.some _ _ h₁) + W.reducePoint A (.some _ _ h₂) := by
  by_cases hx : residue A x₁ = residue A x₂
  · apply W.reducePoint_add_of_residue_y_ne A x₁ y₁ x₂ y₂ h₁ h₂
    intro hy
    apply hred
    rw [reducePoint_some_map, reducePoint_some_map, Affine.Point.neg_some]
    simp only [Affine.Point.some.injEq]
    exact ⟨hx, hy⟩
  · exact W.reducePoint_add_of_residue_x_ne A x₁ y₁ x₂ y₂ h₁ h₂ hx
end WeierstrassCurve
