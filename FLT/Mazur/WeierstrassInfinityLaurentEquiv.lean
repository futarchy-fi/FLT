/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityLaurentMaps
public import FLT.Mazur.LaurentNilpotentReparametrization

/-!
# The full nilpotent infinity chart is a Laurent algebra

Uniqueness of the vertical cubic solution proves both inverse identities.
No reduction, localization of the original chart, or flatness assumption is used.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (ha : IsUnit W.a₁)
  (I : Ideal R) (hI : IsNilpotent I)
  (h2 : W.a₂ ∈ I) (h3 : W.a₃ ∈ I) (h4 : W.a₄ ∈ I) (h6 : W.a₆ ∈ I)
local notation "B" => Coordinate W 1
local notation "f" => nilpotentInfinityChartToLaurent W ha I hI h2 h3 h4 h6
local notation "g" => nilpotentInfinityLaurentToChart W I hI h2 h3 h4 h6
local notation "x" => splitNodalLaurentX ha.unit
local notation "z" => nilpotentInfinityLaurentZ W ha I hI h2 h3 h4 h6

/-- The reverse Laurent map recovers the full original vertical coordinate. -/
theorem nilpotentInfinityLaurentToChart_z : g z = coord W 1 2 := by
  apply infinityVerticalSolution_unique W I hI h2 h3 h4 h6 (coord W 1 0)
    (nilpotentInfinityLinear_isUnit W I hI h2 h3 h4 h6)
  · have h := congrArg g (infinityVerticalSolution_equation W I hI h2 h3 h4 h6 x
      (nilpotentInfinityLaurent_tangent_isUnit W ha))
    change g (z * _) = g (x ^ 3) at h
    simpa only [map_mul, map_sub, map_add, map_one, map_pow, AlgHom.commutes,
      nilpotentInfinityLaurentToChart_x, nilpotentInfinityLaurentZ] using h
  · exact nilpotentInfinityDenominator_cubic W

/-- The constructed maps compose to the identity on every original chart coordinate. -/
theorem nilpotentInfinityLaurentToChart_comp : (g).comp f = AlgHom.id R B := by
  apply hom_ext
  intro i
  simp only [AlgHom.comp_apply, nilpotentInfinityChartToLaurent_coord, AlgHom.id_apply]
  fin_cases i
  · exact nilpotentInfinityLaurentToChart_x W ha I hI h2 h3 h4 h6
  · change g 1 = coord W 1 1
    rw [map_one, coord_self]
  · exact nilpotentInfinityLaurentToChart_z W ha I hI h2 h3 h4 h6

/-- The reverse composite fixes the Laurent generator and hence every Laurent function. -/
theorem nilpotentInfinityChartToLaurent_comp :
    (f).comp g = AlgHom.id R R[T;T⁻¹] := by
  apply LaurentNilpotentReparametrization.hom_ext_positive
  simp only [AlgHom.comp_apply, nilpotentInfinityLaurentToChart_pos,
    map_add, map_one, map_mul, AlgHom.commutes, nilpotentInfinityChartToLaurent_coord,
    Matrix.cons_val_zero, AlgHom.id_apply, nilpotentInfinityLaurent_tangent]

/-- An explicit equivalence of the full original infinity algebra with the Laurent algebra. -/
def nilpotentInfinityChartLaurentEquiv : B ≃ₐ[R] R[T;T⁻¹] :=
  AlgEquiv.ofAlgHom f g (nilpotentInfinityChartToLaurent_comp W ha I hI h2 h3 h4 h6)
    (nilpotentInfinityLaurentToChart_comp W ha I hI h2 h3 h4 h6)

/-- The forward map is the constructed cubic evaluation. -/
theorem nilpotentInfinityChartLaurentEquiv_toAlgHom :
    (nilpotentInfinityChartLaurentEquiv W ha I hI h2 h3 h4 h6).toAlgHom = f := rfl

/-- The inverse map evaluates at the exact original tangent unit. -/
theorem nilpotentInfinityChartLaurentEquiv_symm_toAlgHom :
    (nilpotentInfinityChartLaurentEquiv W ha I hI h2 h3 h4 h6).symm.toAlgHom = g := rfl

end FLT.Mazur.WeierstrassIntegralChart
