/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticReductionRelation

/-!
# Addition with nonopposite smooth affine reductions

The secant and tangent slope charts give an integral slope whenever the two
smooth affine reductions are not opposites. The reduced cubic may be singular.
-/

@[expose] public section

namespace FLT.Mazur
open IsLocalRing WeierstrassCurve

variable {K : Type*} [Field K] [DecidableEq K] (A : ValuationSubring K)
  (W : WeierstrassCurve A) [DecidableEq (ResidueField A)]

/-- An integral slope compatible with reduction gives compatible addition. -/
theorem reducesTo_add_of_integral_slope (x₁ y₁ x₂ y₂ l : A)
    (h₁ : (W.map (algebraMap A K)).toAffine.Nonsingular (algebraMap A K x₁) (algebraMap A K y₁))
    (h₂ : (W.map (algebraMap A K)).toAffine.Nonsingular (algebraMap A K x₂) (algebraMap A K y₂))
    (hr₁ : (W.map (residue A)).toAffine.Nonsingular (residue A x₁) (residue A y₁))
    (hr₂ : (W.map (residue A)).toAffine.Nonsingular (residue A x₂) (residue A y₂))
    (hxy : ¬ ((algebraMap A K x₁) = algebraMap A K x₂ ∧ (algebraMap A K y₁) =
      (W.map (algebraMap A K)).toAffine.negY (algebraMap A K x₂) (algebraMap A K y₂)))
    (hrxy : ¬ (residue A x₁ = residue A x₂ ∧ residue A y₁ =
      (W.map (residue A)).toAffine.negY (residue A x₂) (residue A y₂)))
    (hl : (W.map (algebraMap A K)).toAffine.slope (algebraMap A K x₁) (algebraMap A K x₂)
      (algebraMap A K y₁) (algebraMap A K y₂) = (algebraMap A K l))
    (hrl : (W.map (residue A)).toAffine.slope (residue A x₁) (residue A x₂)
      (residue A y₁) (residue A y₂) = residue A l) :
    ReducesTo A W (.some _ _ h₁ + .some _ _ h₂) (.some _ _ hr₁ + .some _ _ hr₂) := by
  rw [Affine.Point.add_some hxy, Affine.Point.add_some hrxy]
  simp only [hl, hrl]
  have hx := W.toAffine.map_addX (algebraMap A K) x₁ x₂ l
  have hy := W.toAffine.map_addY (algebraMap A K) x₁ y₁ x₂ l
  change (W.map (algebraMap A K)).toAffine.addX _ _ _ = _ at hx
  change (W.map (algebraMap A K)).toAffine.addY _ _ _ _ = _ at hy
  simp only [hx, hy]
  unfold ReducesTo
  simp only [ValuationSubring.algebraMap_apply]
  rw [projectiveReduction_affine]
  simp only [Affine.Point.toProjective, Projective.Point.fromAffine_some,
    W.toAffine.map_addX (residue A), W.toAffine.map_addY (residue A)]

/-- The secant chart applies when the reduced x-coordinates differ. -/
theorem reducesTo_add_of_residue_x_ne (x₁ y₁ x₂ y₂ : A)
    (h₁ : (W.map (algebraMap A K)).toAffine.Nonsingular (algebraMap A K x₁) (algebraMap A K y₁))
    (h₂ : (W.map (algebraMap A K)).toAffine.Nonsingular (algebraMap A K x₂) (algebraMap A K y₂))
    (hr₁ : (W.map (residue A)).toAffine.Nonsingular (residue A x₁) (residue A y₁))
    (hr₂ : (W.map (residue A)).toAffine.Nonsingular (residue A x₂) (residue A y₂))
    (hx : residue A x₁ ≠ residue A x₂) :
    ReducesTo A W (.some _ _ h₁ + .some _ _ h₂) (.some _ _ hr₁ + .some _ _ hr₂) := by
  have hx' : (algebraMap A K x₁) ≠ algebraMap A K x₂ :=
    fun he => hx (congrArg (residue A) (Subtype.ext he))
  have hu : IsUnit (x₁ - x₂) := (residue_ne_zero_iff_isUnit _).mp (by
    simpa only [map_sub, sub_ne_zero] using hx)
  let l : A := (y₁ - y₂) * ↑hu.unit⁻¹
  apply reducesTo_add_of_integral_slope A W x₁ y₁ x₂ y₂ l h₁ h₂ hr₁ hr₂
    (fun h => hx' h.1) (fun h => hx h.1)
  · rw [Affine.slope_of_X_ne hx']
    simp only [l, map_mul, map_sub, map_units_inv, hu.unit_spec, div_eq_mul_inv]
  · rw [Affine.slope_of_X_ne hx]
    simp only [l, map_mul, map_sub, map_units_inv, hu.unit_spec, div_eq_mul_inv]

/-- The second slope chart covers equal reduced x-coordinates and nonopposite y-coordinates. -/
theorem reducesTo_add_of_residue_y_ne (x₁ y₁ x₂ y₂ : A)
    (h₁ : (W.map (algebraMap A K)).toAffine.Nonsingular (algebraMap A K x₁) (algebraMap A K y₁))
    (h₂ : (W.map (algebraMap A K)).toAffine.Nonsingular (algebraMap A K x₂) (algebraMap A K y₂))
    (hr₁ : (W.map (residue A)).toAffine.Nonsingular (residue A x₁) (residue A y₁))
    (hr₂ : (W.map (residue A)).toAffine.Nonsingular (residue A x₂) (residue A y₂))
    (hy : residue A y₁ ≠
      (W.map (residue A)).toAffine.negY (residue A x₂) (residue A y₂)) :
    ReducesTo A W (.some _ _ h₁ + .some _ _ h₂) (.some _ _ hr₁ + .some _ _ hr₂) := by
  have hy' : (algebraMap A K y₁) ≠ (W.map (algebraMap A K)).toAffine.negY
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
  apply reducesTo_add_of_integral_slope A W x₁ y₁ x₂ y₂ l h₁ h₂ hr₁ hr₂
    (fun h => hy' h.2) (fun h => hy h.2)
  · rw [Affine.slope_eq_of_Y_ne _ h₁.1 h₂.1 hy']
    simp only [l, d, map_mul, map_sub, map_add, map_pow, map_units_inv,
      hu.unit_spec, map_a₁, map_a₂, map_a₄, map_a₃, div_eq_mul_inv]
  · rw [Affine.slope_eq_of_Y_ne _ hr₁.1 hr₂.1 hy]
    simp only [l, d, map_mul, map_sub, map_add, map_pow, map_units_inv,
      hu.unit_spec, map_a₁, map_a₂, map_a₄, map_a₃, div_eq_mul_inv]

/-- Nonopposite smooth affine reductions add compatibly. -/
theorem reducesTo_add_of_residue_ne_neg (x₁ y₁ x₂ y₂ : A)
    (h₁ : (W.map (algebraMap A K)).toAffine.Nonsingular (algebraMap A K x₁) (algebraMap A K y₁))
    (h₂ : (W.map (algebraMap A K)).toAffine.Nonsingular (algebraMap A K x₂) (algebraMap A K y₂))
    (hr₁ : (W.map (residue A)).toAffine.Nonsingular (residue A x₁) (residue A y₁))
    (hr₂ : (W.map (residue A)).toAffine.Nonsingular (residue A x₂) (residue A y₂))
    (hred : ¬ (residue A x₁ = residue A x₂ ∧ residue A y₁ =
      (W.map (residue A)).toAffine.negY (residue A x₂) (residue A y₂))) :
    ReducesTo A W (.some _ _ h₁ + .some _ _ h₂) (.some _ _ hr₁ + .some _ _ hr₂) := by
  by_cases hx : residue A x₁ = residue A x₂
  · exact reducesTo_add_of_residue_y_ne A W x₁ y₁ x₂ y₂ h₁ h₂ hr₁ hr₂
      (fun hy => hred ⟨hx, hy⟩)
  · exact reducesTo_add_of_residue_x_ne A W x₁ y₁ x₂ y₂ h₁ h₂ hr₁ hr₂ hx

end FLT.Mazur
