/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonFirstNodeParameterDescent
public import FLT.Mazur.LaurentPositivePart

/-!
# Polynomial tests for extending nilpotent branch functions across the node

Descent means that both Laurent coefficients are polynomials with matching
constant terms. For a function supported on one branch this becomes the
vanishing of its nonpositive Laurent tail. These tests concern functions,
without assuming any node endomorphism or its reduction.
-/

@[expose] public noncomputable section
open scoped Polynomial LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial LaurentPositivePart LaurentBoundaryVectorField
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
variable (R : Type) [CommRing R]

/-- A pair extends over the split node precisely when it is polynomial and matches at the origin. -/
theorem splitNode_branches_exists_iff (p q : R[T;T⁻¹]) :
    (∃ z : ChartRing (0 : R), leftLaurentMap (0 : R) z = p ∧
      leftLaurentMap (0 : R) (branchSwapMap (0 : R) z) = q) ↔
    ∃ a b : R[X], a.toLaurent = p ∧ b.toLaurent = q ∧ a.coeff 0 = b.coeff 0 := by
  constructor
  · rintro ⟨z, hl, hr⟩
    refine ⟨PolygonNodeEqualizer.first (specialFiberEquiv R z),
      PolygonNodeEqualizer.second (specialFiberEquiv R z), ?_, ?_, ?_⟩
    · exact (AlgHom.congr_fun (specialLeftMap_comparison R) z).trans hl
    · exact (AlgHom.congr_fun (specialRightMap_comparison R) z).trans hr
    · have he := AlgHom.congr_fun (PolygonNodeEqualizer.first_second_agree (R := R))
        (specialFiberEquiv R z)
      change Polynomial.eval 0 (PolygonNodeEqualizer.first (specialFiberEquiv R z)) =
        Polynomial.eval 0 (PolygonNodeEqualizer.second (specialFiberEquiv R z)) at he
      simpa only [← Polynomial.coeff_zero_eq_eval_zero] using he
  · rintro ⟨a, b, ha, hb, hab⟩
    let z : PolygonNodeEqualizer.A (R := R) :=
      ⟨(a, b), (PolygonNodeEqualizer.mem_A _).mpr (by
        simpa only [← Polynomial.coeff_zero_eq_eval_zero] using hab)⟩
    refine ⟨(specialFiberEquiv R).symm z, ?_, ?_⟩
    · have he := AlgHom.congr_fun (specialLeftMap_comparison R)
        ((specialFiberEquiv R).symm z)
      change specialLeftMap R (specialFiberEquiv R ((specialFiberEquiv R).symm z)) = _ at he
      rw [AlgEquiv.apply_symm_apply] at he
      exact he.symm.trans ha
    · have he := AlgHom.congr_fun (specialRightMap_comparison R)
        ((specialFiberEquiv R).symm z)
      change specialRightMap R (specialFiberEquiv R ((specialFiberEquiv R).symm z)) = _ at he
      rw [AlgEquiv.apply_symm_apply] at he
      exact he.symm.trans hb

/-- The full parameter-layer descent test is a pair of polynomial lifts with equal constants. -/
theorem firstNodeBranchSubalgebra_parameter_polynomial_iff (p q : R[T;T⁻¹]) :
    (firstLaurentParameterLift R p, firstLaurentParameterLift R q) ∈
        firstNodeBranchSubalgebra R ↔
      ∃ a b : R[X], a.toLaurent = p ∧ b.toLaurent = q ∧ a.coeff 0 = b.coeff 0 := by
  rw [firstNodeBranchSubalgebra_parameter_iff, splitNode_branches_exists_iff]

/-- A polynomial vanishing at the origin has no nonpositive Laurent tail. -/
theorem boundaryTail_polynomial_zero (p : R[X]) (hp : p.coeff 0 = 0) :
    boundaryTail p.toLaurent = 0 := by
  apply (boundaryTail_eq_zero_iff _).mpr
  intro d hd
  rcases lt_or_eq_of_le hd with hd | rfl
  · exact polynomial_coeff_neg p d hd
  · rw [polynomial_coeff_zero, hp]

/-- Descent of a nilpotent function supported only on the left branch is exactly tail vanishing. -/
theorem firstNodeBranchSubalgebra_parameter_left_iff (p : R[T;T⁻¹]) :
    (firstLaurentParameterLift R p, 0) ∈ firstNodeBranchSubalgebra R ↔
      boundaryTail p = 0 := by
  rw [← firstLaurentParameterLift_zero R,
    firstNodeBranchSubalgebra_parameter_polynomial_iff]
  constructor
  · rintro ⟨a, b, ha, hb, hab⟩
    have hb0 : b = 0 := Polynomial.toLaurent_injective (hb.trans (map_zero _).symm)
    rw [hb0, Polynomial.coeff_zero] at hab
    rw [← ha]
    exact boundaryTail_polynomial_zero R a hab
  · intro hp
    refine ⟨positivePart p, 0, (positivePart_toLaurent_iff p).mpr hp, map_zero _, ?_⟩
    exact positivePart_coeff_zero p

/-- The right-only test retains the same coefficient obstruction on its own branch. -/
theorem firstNodeBranchSubalgebra_parameter_right_iff (p : R[T;T⁻¹]) :
    (0, firstLaurentParameterLift R p) ∈ firstNodeBranchSubalgebra R ↔
      boundaryTail p = 0 := by
  rw [← firstLaurentParameterLift_zero R,
    firstNodeBranchSubalgebra_parameter_polynomial_iff]
  constructor
  · rintro ⟨a, b, ha, hb, hab⟩
    have ha0 : a = 0 := Polynomial.toLaurent_injective (ha.trans (map_zero _).symm)
    rw [ha0, Polynomial.coeff_zero] at hab
    rw [← hb]
    exact boundaryTail_polynomial_zero R b hab.symm
  · intro hp
    refine ⟨0, positivePart p, map_zero _, (positivePart_toLaurent_iff p).mpr hp, ?_⟩
    exact (positivePart_coeff_zero p).symm

end FLT.Mazur.PolygonInfinitesimalStages
