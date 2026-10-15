/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonFirstLaurentPairProduct

/-!
# Reduction of both punctured branches to the original split node

The reduced branch embedding is faithful. The kernel of full pair reduction
is exactly the parameter annihilator, and any two elements of this kernel multiply to zero.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial PolygonScalingNaturality
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
variable (R : Type) [CommRing R]
local notation "S" => Ring R 1
local notation "e" => parameter R 1
local notation "P" => (S)[T;T⁻¹] × (S)[T;T⁻¹]

/-- The faithful pair of branch restrictions on the original reduced split node. -/
def splitNodeBranchPair : ChartRing (0 : R) →ₐ[R] (R[T;T⁻¹] × R[T;T⁻¹]) :=
  (leftLaurentMap (0 : R)).prod
    ((leftLaurentMap (0 : R)).comp (branchSwapMap (0 : R)))

/-- Both reduced branches together detect the entire reduced node ring. -/
theorem splitNodeBranchPair_injective : Function.Injective (splitNodeBranchPair R) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  exact splitNode_branches_zero R z (congrArg Prod.fst hz) (congrArg Prod.snd hz)

/-- Reduction of the full original pair is precisely the original reduced branch pair. -/
theorem firstNodePairReduction_branch (z : ChartRing (e)) :
    firstNodePairReduction R (firstNodeBranchPair R z) =
      splitNodeBranchPair R (firstNodeReduction R z) := by
  apply Prod.ext
  · exact firstNodeReduction_leftLaurent R z
  · change coeffMap (reduction R 1).toRingHom
        (leftLaurentMap (e) (branchSwapMap (e) z)) = _
    rw [firstNodeReduction_leftLaurent, firstNodeReduction_swap]
    rfl

/-- The parameter annihilator is exactly the reduction kernel on full branch pairs. -/
theorem firstNodePairReduction_zero_iff (p : P) :
    firstNodePairReduction R p = 0 ↔ (e) • p = 0 := by
  constructor
  · intro hp
    apply Prod.ext
    · exact (smul_eq_C_mul _ _).trans
        ((firstLaurent_parameter_eq_zero_iff R p.1).mpr (congrArg Prod.fst hp))
    · exact (smul_eq_C_mul _ _).trans
        ((firstLaurent_parameter_eq_zero_iff R p.2).mpr (congrArg Prod.snd hp))
  · intro hp
    apply Prod.ext
    · apply (firstLaurent_parameter_eq_zero_iff R p.1).mp
      exact (smul_eq_C_mul _ _).symm.trans (congrArg Prod.fst hp)
    · apply (firstLaurent_parameter_eq_zero_iff R p.2).mp
      exact (smul_eq_C_mul _ _).symm.trans (congrArg Prod.snd hp)

/-- The entire full reduction kernel, including both branches, has square zero. -/
theorem firstNodePairReduction_kernel_mul (p q : P)
    (hp : firstNodePairReduction R p = 0) (hq : firstNodePairReduction R q = 0) :
    p * q = 0 :=
  firstNodePair_annihilator_mul R p q
    ((firstNodePairReduction_zero_iff R p).mp hp)
    ((firstNodePairReduction_zero_iff R q).mp hq)

end FLT.Mazur.PolygonInfinitesimalStages
