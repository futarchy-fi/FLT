/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonFirstNodeBranchReconstruction
public import FLT.Mazur.PolygonSmoothingReciprocalScaling

/-!
# Reduction of a node map reconstructed from two unit branches

The reductions of the two Laurent units determine the entire closed node
map. In particular reciprocal scaling on the two branches forces the
reconstructed map to have exactly the prescribed original scaling reduction.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial PolygonScalingNaturality
open LaurentCoefficientEvaluation
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
variable (R : Type) [CommRing R]
local notation "S" => Ring R 1
local notation "e" => parameter R 1
local notation "B" => ChartRing (e)

/-- Agreement of both reduced branch functions detects equality on the whole closed node. -/
theorem firstNodeReduction_eq_of_branches (z w : B)
    (hl : coeffMap (reduction R 1).toRingHom (leftLaurentMap (e) z) =
      coeffMap (reduction R 1).toRingHom (leftLaurentMap (e) w))
    (hr : coeffMap (reduction R 1).toRingHom (leftLaurentMap (e) (branchSwapMap (e) z)) =
      coeffMap (reduction R 1).toRingHom (leftLaurentMap (e) (branchSwapMap (e) w))) :
    firstNodeReduction R z = firstNodeReduction R w := by
  apply sub_eq_zero.mp
  apply splitNode_branches_zero R
  · rw [map_sub, ← firstNodeReduction_leftLaurent, ← firstNodeReduction_leftLaurent,
      hl, sub_self]
  · rw [map_sub, map_sub, ← firstNodeReduction_swap, ← firstNodeReduction_swap,
      ← firstNodeReduction_leftLaurent, ← firstNodeReduction_leftLaurent, hr, sub_self]

/-- The two coordinate reductions determine an endomorphism's entire closed reduction. -/
theorem firstNodeReduction_hom_ext (f g : (B) →ₐ[S] (B))
    (hx : firstNodeReduction R (f (leftCoordinate (e))) =
      firstNodeReduction R (g (leftCoordinate (e))))
    (hy : firstNodeReduction R (f (rightCoordinate (e))) =
      firstNodeReduction R (g (rightCoordinate (e)))) (z : B) :
    firstNodeReduction R (f z) = firstNodeReduction R (g z) := by
  let _ := ((algebraMap R (ChartRing (0 : R))).comp (reduction R 1).toRingHom).toAlgebra
  let r : (B) →ₐ[S] ChartRing (0 : R) :=
    { firstNodeReduction R with commutes' s := ringMap_scalar .. }
  exact AlgHom.congr_fun (chartRing_hom_ext (e) (r.comp f) (r.comp g) hx hy) z

variable (u v : ((Ring R 1)[T;T⁻¹])ˣ)
  (hx : firstNodeBranchLeftImage R u v ∈ firstNodeBranchSubalgebra R)
  (hy : firstNodeBranchRightImage R u v ∈ firstNodeBranchSubalgebra R)
  (a : (Ring R 1)ˣ)
  (hu : coeffMap (reduction R 1).toRingHom u.val =
    C (reduction R 1 a.val) * T 1)
  (hv : coeffMap (reduction R 1).toRingHom v.val =
    C (reduction R 1 a⁻¹.val) * T 1)

include hu hv in
/-- Reconstruction retains the prescribed reciprocal scaling on every closed-node function. -/
theorem firstNodeBranchReconstruct_reduction (z : B) :
    firstNodeReduction R (firstNodeBranchReconstruct R u v hx hy z) =
      firstNodeReduction R (reciprocalScale (e) a z) := by
  have hred : (reduction R 1).toRingHom (e) = 0 := reduction_parameter R 1
  apply firstNodeReduction_hom_ext R _ _ ?_ ?_ z
  · apply firstNodeReduction_eq_of_branches R
    · have he := congrArg Prod.fst (firstNodeBranchReconstruct_left R u v hx hy)
      change leftLaurentMap (e) _ = u.val at he
      rw [he, hu]
      simp only [reciprocalScale_left, map_mul, AlgHom.commutes, ← C_eq_algebraMap,
        leftLaurentMap_left, coeffMap_C, coeffMap_T]
      rfl
    · have he := congrArg Prod.snd (firstNodeBranchReconstruct_left R u v hx hy)
      change leftLaurentMap (e) (branchSwapMap (e) _) = C (e) * v⁻¹.val at he
      rw [he]
      simp only [reciprocalScale_left, map_mul, AlgHom.commutes, ← C_eq_algebraMap,
        branchSwapMap_left, leftLaurentMap_right, coeffMap_C, hred, map_zero,
        zero_mul, mul_zero]
  · apply firstNodeReduction_eq_of_branches R
    · have he := congrArg Prod.fst (firstNodeBranchReconstruct_right R u v hx hy)
      change leftLaurentMap (e) _ = C (e) * u⁻¹.val at he
      rw [he]
      simp only [reciprocalScale_right, map_mul, AlgHom.commutes, ← C_eq_algebraMap,
        leftLaurentMap_right, coeffMap_C, hred, map_zero, zero_mul, mul_zero]
    · have he := congrArg Prod.snd (firstNodeBranchReconstruct_right R u v hx hy)
      change leftLaurentMap (e) (branchSwapMap (e) _) = v.val at he
      rw [he, hv]
      simp only [reciprocalScale_right, map_mul, AlgHom.commutes, ← C_eq_algebraMap,
        branchSwapMap_right, leftLaurentMap_left, coeffMap_C, coeffMap_T]
      rfl

end FLT.Mazur.PolygonInfinitesimalStages
