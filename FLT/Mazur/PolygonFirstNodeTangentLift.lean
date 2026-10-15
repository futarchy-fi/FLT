/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonFirstNodeEndomorphism

/-!
# Lifting split-node vector fields to the actual first smoothing node

Every derivation of the original split node constructs an endomorphism of
xy = e over R[e]/e². Lift its two coordinate values and multiply by e;
the tangent equation proves the original smoothing equation exactly.
The result reduces to the identity on the entire node algebra.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] PolygonSmoothing.relationIdeal
variable (R : Type) [CommRing R]
local notation "S" => Ring R 1
local notation "e" => parameter R 1
local notation "B" => ChartRing (e)
local notation "N" => ChartRing (0 : R)

/-- A selected lift of an arbitrary original split-node function. -/
def firstNodeFunctionLift (z : N) : B :=
  Classical.choose (firstNodeReduction_surjective R z)

/-- The selected lift retains the entire original function after reduction. -/
theorem firstNodeFunctionLift_reduction (z : N) :
    firstNodeReduction R (firstNodeFunctionLift R z) = z :=
  Classical.choose_spec (firstNodeReduction_surjective R z)

/-- The parameter-weighted lift is independent of all choices of representatives. -/
theorem firstNodeFunctionLift_weighted (z : N) (a : B)
    (ha : firstNodeReduction R a = z) :
    (e) • firstNodeFunctionLift R z = (e) • a := by
  apply sub_eq_zero.mp
  rw [← smul_sub, firstNode_parameter_annihilator, (firstNodeReduction R).map_sub,
    firstNodeFunctionLift_reduction, ha, sub_self]

local notation "L" => firstNodeFunctionLift R
local notation "t" => algebraMap (S) (B) (e)

/-- The lifted coordinates satisfy xy = e, including the nilpotent coefficient. -/
theorem firstNodeTangentLift_relation (d : Derivation R (N) (N)) :
    (leftCoordinate (e) + (t) * L (d (leftCoordinate (0 : R)))) *
      (rightCoordinate (e) + (t) * L (d (rightCoordinate (0 : R)))) = (t) := by
  have ht : (t) ^ 2 = 0 := firstNode_parameter_sq R
  have hr : (e) • (leftCoordinate (e) * L (d (rightCoordinate (0 : R))) +
      rightCoordinate (e) * L (d (leftCoordinate (0 : R)))) = 0 := by
    rw [firstNode_parameter_annihilator, (firstNodeReduction R).map_add,
      (firstNodeReduction R).map_mul,
      (firstNodeReduction R).map_mul,
      firstNodeReduction_left, firstNodeReduction_right,
      firstNodeFunctionLift_reduction, firstNodeFunctionLift_reduction]
    exact derivation_coordinate_relation (0 : R) d
  have hr' := (Algebra.smul_def (e) (leftCoordinate (e) *
    L (d (rightCoordinate (0 : R))) +
    rightCoordinate (e) * L (d (leftCoordinate (0 : R))))).symm.trans hr
  have hxy := coordinate_relation (e)
  linear_combination hxy + hr' + L (d (leftCoordinate (0 : R))) * L (d (rightCoordinate (0
      : R))) * ht

/-- An actual endomorphism of the first smoothing node, constructed from the vector field. -/
def firstNodeTangentLift (d : Derivation R (N) (N)) : (B) →ₐ[S] (B) :=
  evaluate (e) (leftCoordinate (e) + (t) * L (d (leftCoordinate (0 : R))))
    (rightCoordinate (e) + (t) * L (d (rightCoordinate (0 : R))))
      (firstNodeTangentLift_relation R d)

/-- The first coordinate of the constructed endomorphism. -/
theorem firstNodeTangentLift_left (d : Derivation R (N) (N)) :
    firstNodeTangentLift R d (leftCoordinate (e)) = leftCoordinate (e) + (t) * L (d
      (leftCoordinate (0 : R))) :=
  evaluate_left ..

/-- The second coordinate of the constructed endomorphism. -/
theorem firstNodeTangentLift_right (d : Derivation R (N) (N)) :
    firstNodeTangentLift R d (rightCoordinate (e)) = rightCoordinate (e) + (t) * L (d
      (rightCoordinate (0 : R))) :=
  evaluate_right ..

/-- Reduction kills the actual smoothing parameter, including inside the node ring. -/
theorem firstNodeReduction_parameter : firstNodeReduction R (t) = 0 := by
  rw [firstNodeReduction, ringMap_scalar]
  exact (congrArg (algebraMap R (N)) (reduction_parameter R 1)).trans (map_zero _)

/-- The constructed lift reduces to the identity on every node function. -/
theorem firstNodeTangentLift_reduction (d : Derivation R (N) (N)) (z : B) :
    firstNodeReduction R (firstNodeTangentLift R d z) = firstNodeReduction R z := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  induction p using MvPolynomial.induction_on with
  | C s =>
    change firstNodeReduction R (firstNodeTangentLift R d (algebraMap (S) (B) s)) = _
    rw [AlgHom.commutes]
    rfl
  | add p q hp hq =>
    simp only [(Ideal.Quotient.mk (relationIdeal (e))).map_add,
      map_add (firstNodeTangentLift R d), (firstNodeReduction R).map_add, hp, hq]
  | mul_X p i hp =>
    have hx : firstNodeReduction R
        (firstNodeTangentLift R d (Ideal.Quotient.mk _ (MvPolynomial.X i))) =
        firstNodeReduction R (Ideal.Quotient.mk _ (MvPolynomial.X i)) := by
      fin_cases i
      · change firstNodeReduction R (firstNodeTangentLift R d (leftCoordinate (e))) = _
        rw [firstNodeTangentLift_left, (firstNodeReduction R).map_add, (firstNodeReduction
      R).map_mul,
          firstNodeReduction_parameter, zero_mul, add_zero]
        rfl
      · change firstNodeReduction R (firstNodeTangentLift R d (rightCoordinate (e))) = _
        rw [firstNodeTangentLift_right, (firstNodeReduction R).map_add,
      (firstNodeReduction R).map_mul,
          firstNodeReduction_parameter, zero_mul, add_zero]
        rfl
    simp only [(Ideal.Quotient.mk (relationIdeal (e))).map_mul,
      map_mul (firstNodeTangentLift R d), (firstNodeReduction R).map_mul, hp, hx]

end FLT.Mazur.PolygonInfinitesimalStages
