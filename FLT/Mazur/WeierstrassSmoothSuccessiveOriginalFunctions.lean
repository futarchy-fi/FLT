/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothSuccessiveIntegralTransport
public import FLT.Mazur.WeierstrassSuccessiveXModificationGeometry

/-!
# Original cubic functions under integral successive transport

The product-scale equation comparison preserves the original x and y,
and hence every original cubic function, in the actual horizontal fraction ring.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassIntegralChart
open WeierstrassModificationReesCoordinates
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} {k : ℕ}
  (d : WeierstrassDividedDepth.Data W π (k + 1)) (hπ : π ≠ 0)
local notation "H" => HorizontalSourceRing W (π ^ (k + 1))
local notation "B" => WeierstrassModificationX.Coordinate W (π ^ k * π) d.b3 d.b4 d.b6
local notation "E" => WeierstrassModificationX.horizontalReesChartEquiv W (π ^ (k + 1))
  d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6 (pow_ne_zero _ hπ)

/-- The equation comparison retains the original horizontal cubic function. -/
theorem successiveHorizontalEquationMap_x :
    successiveHorizontalEquationMap d hπ
      (WeierstrassModificationX.x W (π ^ k * π) d.b3 d.b4 d.b6) =
        algebraMap (Coordinate W 2) H (coord W 2 0) := by
  have hx : E (WeierstrassModificationX.x W (π ^ (k + 1)) d.b3 d.b4 d.b6) =
      algebraMap (Coordinate W 2) H (coord W 2 0) := by
    apply Subtype.ext
    change _ = algebraMap (Coordinate W 2)
      (WeierstrassModificationX.OriginalHorizontalOpen W) _
    simpa only [WeierstrassModificationX.fromOriginal_x] using
      WeierstrassModificationX.horizontalReesChartEquiv_fromOriginal W (π ^ (k + 1))
        d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6 (pow_ne_zero _ hπ) (coord W 2 0)
  rw [← hx]
  simp only [WeierstrassModificationX.x, map_sub, map_add, map_mul, map_pow,
    AlgHom.commutes, AlgEquiv.commutes, successiveHorizontalEquationMap_t,
    successiveHorizontalEquationMap_v, horizontalEquiv_t, horizontalEquiv_v]

/-- The slope comparison retains the complete original vertical cubic function. -/
theorem successiveHorizontalEquationMap_y :
    successiveHorizontalEquationMap d hπ
      (WeierstrassModificationX.y W (π ^ k * π) d.b3 d.b4 d.b6) =
        algebraMap (Coordinate W 2) H (coord W 2 1) := by
  have hy : E (WeierstrassModificationX.y W (π ^ (k + 1)) d.b3 d.b4 d.b6) =
      algebraMap (Coordinate W 2) H (coord W 2 1) := by
    apply Subtype.ext
    change _ = algebraMap (Coordinate W 2)
      (WeierstrassModificationX.OriginalHorizontalOpen W) _
    simpa only [WeierstrassModificationX.fromOriginal_y] using
      WeierstrassModificationX.horizontalReesChartEquiv_fromOriginal W (π ^ (k + 1))
        d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6 (pow_ne_zero _ hπ) (coord W 2 1)
  rw [← hy]
  simp only [WeierstrassModificationX.y, WeierstrassModificationX.x,
    map_mul, map_sub, map_add, map_pow, AlgHom.commutes, AlgEquiv.commutes,
    successiveHorizontalEquationMap_t, successiveHorizontalEquationMap_v,
    horizontalEquiv_t, horizontalEquiv_v]

variable (h3 : W.a₃ = (π ^ k * π) * d.b3) (h4 : W.a₄ = (π ^ k * π) * d.b4)
  (h6 : W.a₆ = (π ^ k * π) ^ 2 * d.b6)

/-- Every original cubic function survives the product-scale equation comparison. -/
theorem successiveHorizontalEquationMap_fromOriginal :
    (successiveHorizontalEquationMap d hπ).comp
      (WeierstrassModificationX.fromOriginal W (π ^ k * π) d.b3 d.b4 d.b6 h3 h4 h6) =
        IsScalarTower.toAlgHom R (Coordinate W 2) H := by
  apply hom_ext
  intro i
  fin_cases i
  · change successiveHorizontalEquationMap d hπ
      (WeierstrassModificationX.fromOriginal W (π ^ k * π) d.b3 d.b4 d.b6 h3 h4 h6
        (coord W 2 0)) = _
    rw [WeierstrassModificationX.fromOriginal_x, successiveHorizontalEquationMap_x]
    rfl
  · change successiveHorizontalEquationMap d hπ
      (WeierstrassModificationX.fromOriginal W (π ^ k * π) d.b3 d.b4 d.b6 h3 h4 h6
        (coord W 2 1)) = _
    rw [WeierstrassModificationX.fromOriginal_y, successiveHorizontalEquationMap_y]
    rfl
  · have hc : coord W 2 (⟨2, by decide⟩ : Fin 3) = 1 := coord_self W 2
    rw [hc, map_one, map_one]

end FLT.Mazur.WeierstrassIntegralChart
