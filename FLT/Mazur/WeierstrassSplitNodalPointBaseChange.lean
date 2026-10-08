/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitNodalPointMultiplication

/-!
# The unit point parametrization commutes with coefficient extension

Transport between equal coefficient equations preserves the actual projective
point class and its group law. Unit evaluations commute with this transport,
so multiplication compatibility holds over every coefficient algebra field.
-/

@[expose] public noncomputable section

open WeierstrassCurve WeierstrassCurve.Projective

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

/-- Equal equations identify their actual projective point groups. -/
def projectivePointEquationCongr {K : Type u} [Field K]
    {W V : WeierstrassCurve K} (h : W = V) : W.toProjective.Point ≃+ V.toProjective.Point :=
  h ▸ AddEquiv.refl _

/-- Equation transport preserves the underlying homogeneous point class. -/
theorem projectivePointEquationCongr_point {K : Type u} [Field K]
    {W V : WeierstrassCurve K} (h : W = V) (P : W.toProjective.Point) :
    (projectivePointEquationCongr h P).point = P.point := by
  subst V
  rfl

variable {R K : Type u} [CommRing R] [Field K] [Algebra R K] (a : Rˣ)

/-- The extended equation is the nodal equation with the extended unit coefficient. -/
theorem splitNodalEquation_map_unit :
    (splitNodalEquation a).map (algebraMap R K) =
      (splitNodalEquation (Units.map (algebraMap R K) a)).map (algebraMap K K) := by
  ext <;> simp [splitNodalEquation, WeierstrassCurve.map]

/-- The point group comparison for the actual coefficient extension. -/
def splitNodalPointBaseEquiv :
    ((splitNodalEquation a).map (algebraMap R K)).toProjective.Point ≃+
      ((splitNodalEquation (Units.map (algebraMap R K) a)).map
        (algebraMap K K)).toProjective.Point :=
  projectivePointEquationCongr (splitNodalEquation_map_unit a)

/-- Unit evaluation gives the identical homogeneous point after extending coefficients. -/
theorem splitNodalPointBaseEquiv_unit (t : Kˣ) :
    splitNodalPointBaseEquiv a (splitNodalUnitPointEquiv a t) =
      splitNodalUnitPointEquiv (R := K) (Units.map (algebraMap R K) a) t := by
  apply Point.ext
  rw [splitNodalPointBaseEquiv, projectivePointEquationCongr_point]
  change (⟦_⟧ : PointClass K) = ⟦_⟧
  congr 1
  funext i
  fin_cases i <;>
    simp [splitNodalUnitChartEquiv, splitNodalUnitChart, splitNodalLaurentX, splitNodalLaurentZ,
      Function.comp_apply]

/-- Multiplication compatibility holds after every coefficient extension to a field. -/
theorem splitNodalUnitPoint_relative_mul (s t : Kˣ) :
    splitNodalUnitPointEquiv a (s * t) =
      splitNodalUnitPointEquiv a s + splitNodalUnitPointEquiv a t := by
  apply (splitNodalPointBaseEquiv a).injective
  rw [map_add, splitNodalPointBaseEquiv_unit, splitNodalPointBaseEquiv_unit,
    splitNodalPointBaseEquiv_unit, splitNodalUnitPoint_mul]

/-- The inverse parameter preserves arbitrary sums over every coefficient field algebra. -/
theorem splitNodalUnitPoint_relative_symm_add
    (P Q : ((splitNodalEquation a).map (algebraMap R K)).toProjective.Point) :
    (splitNodalUnitPointEquiv a).symm (P + Q) =
      (splitNodalUnitPointEquiv a).symm P * (splitNodalUnitPointEquiv a).symm Q := by
  apply (splitNodalUnitPointEquiv a).injective
  simp only [Equiv.apply_symm_apply, splitNodalUnitPoint_relative_mul]

end FLT.Mazur.WeierstrassIntegralChart
