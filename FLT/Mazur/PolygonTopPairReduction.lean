/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonFirstPairReduction
public import FLT.Mazur.PolygonTopNodeLaurent
public import FLT.Mazur.PolygonTopNodeActionDefect

/-!
# Closed reduction of both full higher branches

The original source pair reduces to the faithful split-node pair.
Every parameter-annihilated pair reduces to zero at all positive stages.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial PolygonScalingNaturality
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
variable (R : Type) [CommRing R] (m : ℕ)
local notation "S" => Ring R (m + 1)
local notation "e" => parameter R (m + 1)
local notation "L" => (S)[T;T⁻¹]

/-- Closed reduction on both entire punctured branches. -/
def topNodePairReduction : ((L) × (L)) →+* (R[T;T⁻¹] × R[T;T⁻¹]) :=
  (coeffMap (reduction R (m + 1)).toRingHom).prodMap
    (coeffMap (reduction R (m + 1)).toRingHom)

/-- Closed reduction respects the interchange of the original node coordinates. -/
theorem topNodeReduction_swap (z : ChartRing (e)) :
    topNodeReduction R m (branchSwapMap (e) z) =
      branchSwapMap (0 : R) (topNodeReduction R m z) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  induction p using MvPolynomial.induction_on with
  | C s =>
    change topNodeReduction R m (branchSwapMap (e) (algebraMap (S) (ChartRing (e)) s)) =
      branchSwapMap (0 : R) (topNodeReduction R m (algebraMap (S) (ChartRing (e)) s))
    rw [AlgHom.commutes, topNodeReduction, ringMap_scalar, AlgHom.commutes]
  | add p q hp hq =>
    simp only [(Ideal.Quotient.mk (relationIdeal (e))).map_add,
      map_add (branchSwapMap (e)), map_add (branchSwapMap (0 : R)),
      (topNodeReduction R m).map_add, hp, hq]
  | mul_X p i hp =>
    have hi : topNodeReduction R m
        (branchSwapMap (e) (Ideal.Quotient.mk _ (MvPolynomial.X i))) =
        branchSwapMap (0 : R)
          (topNodeReduction R m (Ideal.Quotient.mk _ (MvPolynomial.X i))) := by
      fin_cases i
      · change topNodeReduction R m (branchSwapMap (e) (leftCoordinate (e))) =
          branchSwapMap (0 : R) (topNodeReduction R m (leftCoordinate (e)))
        rw [branchSwapMap_left, topNodeReduction_right,
          topNodeReduction_left, branchSwapMap_left]
      · change topNodeReduction R m (branchSwapMap (e) (rightCoordinate (e))) =
          branchSwapMap (0 : R) (topNodeReduction R m (rightCoordinate (e)))
        rw [branchSwapMap_right, topNodeReduction_left,
          topNodeReduction_right, branchSwapMap_right]
    simp only [(Ideal.Quotient.mk (relationIdeal (e))).map_mul,
      map_mul (branchSwapMap (e)), map_mul (branchSwapMap (0 : R)),
      (topNodeReduction R m).map_mul, hp, hi]

/-- Both original higher branches reduce to the same full split node. -/
theorem topNodePairReduction_branch (z : ChartRing (e)) :
    topNodePairReduction R m (stageNodeBranchPair R (m + 1) z) =
      splitNodeBranchPair R (topNodeReduction R m z) := by
  apply Prod.ext
  · exact topNodeReduction_leftLaurent R m z
  · change coeffMap (reduction R (m + 1)).toRingHom
        (leftLaurentMap (e) (branchSwapMap (e) z)) = _
    rw [topNodeReduction_leftLaurent, topNodeReduction_swap]
    rfl

/-- A Laurent function killed by the actual parameter has zero closed reduction. -/
theorem topLaurentReduction_annihilator (p : L) (hp : C (e) * p = 0) :
    coeffMap (reduction R (m + 1)).toRingHom p = 0 := by
  rw [topLaurent_annihilator_reconstruct R m p hp, map_mul, coeffMap_C]
  change C (reduction R (m + 1) ((e) ^ (m + 1))) * _ = 0
  rw [map_pow, reduction_parameter, zero_pow (Nat.succ_ne_zero m), map_zero, zero_mul]

/-- Full parameter-annihilated pairs disappear under closed reduction. -/
theorem topNodePairReduction_annihilator (p : (L) × (L)) (hp : (e) • p = 0) :
    topNodePairReduction R m p = 0 := by
  apply Prod.ext
  · exact topLaurentReduction_annihilator R m p.1
      ((smul_eq_C_mul _ _).symm.trans (congrArg Prod.fst hp))
  · exact topLaurentReduction_annihilator R m p.2
      ((smul_eq_C_mul _ _).symm.trans (congrArg Prod.snd hp))

end FLT.Mazur.PolygonInfinitesimalStages
