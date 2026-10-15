/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonFirstNodeBranchReconstruction
public import FLT.Mazur.PolygonFirstNodeTangentLift
public import FLT.Mazur.PolygonStageCoefficientChange

/-!
# Exact descent of the parameter layer from the two punctured branches

A pair of parameter-weighted Laurent functions extends across the actual
first smoothing node exactly when the unweighted functions come from the
reduced node. The proof retains the full nilpotent layer and constructs a
lift using the original reduction map.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial PolygonScalingNaturality
open PolygonInfinitesimal LaurentCoefficientEvaluation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] PolygonSmoothing.relationIdeal
variable (R : Type) [CommRing R]
local notation "S" => Ring R 1
local notation "e" => parameter R 1
local notation "B" => ChartRing (e)
local notation "N" => ChartRing (0 : R)

/-- The parameter layer of a Laurent branch, with the original residue coefficients. -/
def firstLaurentParameterLift (p : R[T;T⁻¹]) : (S)[T;T⁻¹] :=
  C (e) * coeffMap (algebraMap R (S)) p

/-- No Laurent coefficient is lost when lifted to the first parameter layer. -/
theorem firstLaurentParameterLift_injective :
    Function.Injective (firstLaurentParameterLift R) := by
  intro p q he
  ext d
  have hd := congrArg (fun a : (S)[T;T⁻¹] ↦ a.coeff d) he
  simp only [firstLaurentParameterLift, ← smul_eq_C_mul,
    AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul, coeffMap_coeff] at hd
  exact parameter_scalar_one_injective hd

/-- The parameter-layer lift is additive. -/
theorem firstLaurentParameterLift_add (p q : R[T;T⁻¹]) :
    firstLaurentParameterLift R (p + q) =
      firstLaurentParameterLift R p + firstLaurentParameterLift R q := by
  simp only [firstLaurentParameterLift, map_add, mul_add]

/-- Its zero value is zero. -/
theorem firstLaurentParameterLift_zero : firstLaurentParameterLift R 0 = 0 := by
  rw [firstLaurentParameterLift, map_zero, mul_zero]

/-- Its closed reduction vanishes on the entire Laurent branch. -/
theorem firstLaurentParameterLift_reduction (p : R[T;T⁻¹]) :
    coeffMap (reduction R 1).toRingHom (firstLaurentParameterLift R p) = 0 := by
  have he : (reduction R 1).toRingHom (e) = 0 := reduction_parameter R 1
  rw [firstLaurentParameterLift, map_mul, coeffMap_C, he, map_zero, zero_mul]

/-- Restriction of a weighted node function retains its complete reduced branch function. -/
theorem firstNodeBranchPair_parameter (z : B) :
    firstNodeBranchPair R ((e) • z) =
      (firstLaurentParameterLift R (leftLaurentMap (0 : R) (firstNodeReduction R z)),
        firstLaurentParameterLift R
          (leftLaurentMap (0 : R) (branchSwapMap (0 : R) (firstNodeReduction R z)))) := by
  rw [Algebra.smul_def (e) z]
  apply Prod.ext
  · change leftLaurentMap (e) (algebraMap (S) (B) (e) * z) = _
    rw [map_mul, AlgHom.commutes, ← C_eq_algebraMap,
      firstLaurent_parameter_reduction, firstNodeReduction_leftLaurent]
    rfl
  · change leftLaurentMap (e) (branchSwapMap (e) (algebraMap (S) (B) (e) * z)) = _
    rw [map_mul, AlgHom.commutes, map_mul, AlgHom.commutes,
      ← C_eq_algebraMap, firstLaurent_parameter_reduction,
      firstNodeReduction_leftLaurent, firstNodeReduction_swap]
    rfl

/-- Descent of a nilpotent pair is equivalent to descent of its reduced coefficient pair. -/
theorem firstNodeBranchSubalgebra_parameter_iff (p q : R[T;T⁻¹]) :
    (firstLaurentParameterLift R p, firstLaurentParameterLift R q) ∈
        firstNodeBranchSubalgebra R ↔
      ∃ z : N, leftLaurentMap (0 : R) z = p ∧
        leftLaurentMap (0 : R) (branchSwapMap (0 : R) z) = q := by
  constructor
  · rintro ⟨z, hz⟩
    change firstNodeBranchPair R z = _ at hz
    have hl := congrArg Prod.fst hz
    have hr := congrArg Prod.snd hz
    change leftLaurentMap (e) z = firstLaurentParameterLift R p at hl
    change leftLaurentMap (e) (branchSwapMap (e) z) = firstLaurentParameterLift R q at hr
    have hz0 : firstNodeReduction R z = 0 := by
      apply splitNode_branches_zero R
      · rw [← firstNodeReduction_leftLaurent, hl, firstLaurentParameterLift_reduction]
      · rw [← firstNodeReduction_swap, ← firstNodeReduction_leftLaurent, hr,
          firstLaurentParameterLift_reduction]
    obtain ⟨w, hw⟩ := (firstNodeReduction_zero_iff R z).mp hz0
    rw [← hw, firstNodeBranchPair_parameter] at hz
    exact ⟨firstNodeReduction R w,
      firstLaurentParameterLift_injective R (congrArg Prod.fst hz),
      firstLaurentParameterLift_injective R (congrArg Prod.snd hz)⟩
  · rintro ⟨z, hl, hr⟩
    refine ⟨(e) • firstNodeFunctionLift R z, ?_⟩
    change firstNodeBranchPair R ((e) • firstNodeFunctionLift R z) = _
    rw [firstNodeBranchPair_parameter, firstNodeFunctionLift_reduction, hl, hr]

end FLT.Mazur.PolygonInfinitesimalStages
