/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonFirstNodeLaurent

/-!
# The first smoothing node inside its two full Laurent branches

The pair of punctured restrictions is injective even on the nilpotent
thickening. The proof first detects the reduced function and then detects
its parameter coefficient. Thus the image is the actual node algebra,
without discarding any first-order information at the node.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial PolygonScalingNaturality LaurentCoefficientEvaluation
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
variable (R : Type) [CommRing R]
local notation "S" => Ring R 1
local notation "e" => parameter R 1
local notation "B" => ChartRing (e)

/-- Reduction commutes with interchanging the original node coordinates. -/
theorem firstNodeReduction_swap (z : B) :
    firstNodeReduction R (branchSwapMap (e) z) =
      branchSwapMap (0 : R) (firstNodeReduction R z) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  induction p using MvPolynomial.induction_on with
  | C s =>
    change firstNodeReduction R (branchSwapMap (e) (algebraMap (S) (B) s)) =
      branchSwapMap (0 : R) (firstNodeReduction R (algebraMap (S) (B) s))
    rw [AlgHom.commutes, firstNodeReduction, ringMap_scalar, AlgHom.commutes]
  | add p q hp hq =>
    simp only [(firstNodeReduction R).map_add, map_add, hp, hq]
  | mul_X p i hp =>
    have hi : firstNodeReduction R
        (branchSwapMap (e) (Ideal.Quotient.mk _ (MvPolynomial.X i))) =
        branchSwapMap (0 : R)
          (firstNodeReduction R (Ideal.Quotient.mk _ (MvPolynomial.X i))) := by
      fin_cases i
      · change firstNodeReduction R (branchSwapMap (e) (leftCoordinate (e))) =
          branchSwapMap (0 : R) (firstNodeReduction R (leftCoordinate (e)))
        rw [branchSwapMap_left, firstNodeReduction_right,
          firstNodeReduction_left, branchSwapMap_left]
      · change firstNodeReduction R (branchSwapMap (e) (rightCoordinate (e))) =
          branchSwapMap (0 : R) (firstNodeReduction R (rightCoordinate (e)))
        rw [branchSwapMap_right, firstNodeReduction_left,
          firstNodeReduction_right, branchSwapMap_right]
    simp only [(firstNodeReduction R).map_mul, map_mul, hp, hi]

/-- Both punctured branches detect every function on the original reduced node. -/
theorem splitNode_branches_zero (z : ChartRing (0 : R))
    (hl : leftLaurentMap (0 : R) z = 0)
    (hr : leftLaurentMap (0 : R) (branchSwapMap (0 : R) z) = 0) : z = 0 := by
  apply (specialFiberEquiv R).injective
  apply Subtype.ext
  apply Prod.ext
  · apply Polynomial.toLaurent_injective
    exact (AlgHom.congr_fun (specialLeftMap_comparison R) z).trans hl
  · apply Polynomial.toLaurent_injective
    exact (AlgHom.congr_fun (specialRightMap_comparison R) z).trans hr

/-- Parameter multiplication on a Laurent branch detects its entire reduced function. -/
theorem firstLaurent_parameter_eq_zero_iff (p : (S)[T;T⁻¹]) :
    C (e) * p = 0 ↔ coeffMap (reduction R 1).toRingHom p = 0 := by
  constructor
  · intro hp
    ext d
    have hd := congrArg (fun q : (S)[T;T⁻¹] ↦ q.coeff d) hp
    simp only [← smul_eq_C_mul, AddMonoidAlgebra.coeff_smul_apply,
      smul_eq_mul, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hd
    rw [coeffMap_coeff, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    exact (parameter_last_mul_eq_zero_iff R 0 (p.coeff d)).mp
      (by simpa only [Nat.zero_add, pow_one] using hd)
  · intro hp
    rw [firstLaurent_parameter_reduction, hp, map_zero, mul_zero]

/-- The full first node, including its parameter layer, is detected on its two branches. -/
theorem firstNode_branches_zero (z : B)
    (hl : leftLaurentMap (e) z = 0)
    (hr : leftLaurentMap (e) (branchSwapMap (e) z) = 0) : z = 0 := by
  have hz : firstNodeReduction R z = 0 := by
    apply splitNode_branches_zero R
    · rw [← firstNodeReduction_leftLaurent, hl, map_zero]
    · rw [← firstNodeReduction_swap, ← firstNodeReduction_leftLaurent, hr, map_zero]
  obtain ⟨a, ha⟩ := (firstNodeReduction_zero_iff R z).mp hz
  have ha' : algebraMap (S) (B) (e) * a = z := (Algebra.smul_def (e) a).symm.trans ha
  have hal : C (e) * leftLaurentMap (e) a = 0 := by
    have he := congrArg (leftLaurentMap (e)) ha'
    rw [map_mul, AlgHom.commutes] at he
    exact he.trans hl
  have har : C (e) * leftLaurentMap (e) (branchSwapMap (e) a) = 0 := by
    have he := congrArg (fun b ↦ leftLaurentMap (e) (branchSwapMap (e) b)) ha'
    rw [map_mul, AlgHom.commutes, map_mul, AlgHom.commutes] at he
    exact he.trans hr
  have ha0 : firstNodeReduction R a = 0 := by
    apply splitNode_branches_zero R
    · rw [← firstNodeReduction_leftLaurent]
      exact (firstLaurent_parameter_eq_zero_iff R _).mp hal
    · rw [← firstNodeReduction_swap, ← firstNodeReduction_leftLaurent]
      exact (firstLaurent_parameter_eq_zero_iff R _).mp har
  exact ha.symm.trans ((firstNode_parameter_annihilator R a).mpr ha0)

/-- The actual simultaneous restriction to the two punctured branches. -/
def firstNodeBranchPair : (B) →ₐ[S] ((S)[T;T⁻¹] × (S)[T;T⁻¹]) :=
  (leftLaurentMap (e)).prod ((leftLaurentMap (e)).comp (branchSwapMap (e)))

/-- The pair embedding retains all original node functions and all nilpotent coefficients. -/
theorem firstNodeBranchPair_injective : Function.Injective (firstNodeBranchPair R) := by
  intro z w he
  apply sub_eq_zero.mp
  apply firstNode_branches_zero R
  · exact (map_sub _ z w).trans (sub_eq_zero.mpr (congrArg Prod.fst he))
  · rw [map_sub, map_sub]
    exact sub_eq_zero.mpr (congrArg Prod.snd he)

end FLT.Mazur.PolygonInfinitesimalStages
