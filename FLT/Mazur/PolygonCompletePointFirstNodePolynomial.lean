/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointFirstIncomingTail
public import FLT.Mazur.PolygonCompletePointFirstCentralCoefficients
public import FLT.Mazur.PolygonCompletePointNodeLaurentReconstruction

/-!
# Both branches of the retained quadratic and cubic in the original node ring

These are full node-ring identities, not just outgoing Laurent equalities.
The remaining incoming coefficient is explicitly retained on each section.
-/

@[expose] public noncomputable section
open AlgebraicGeometry Scheme.Modules
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing FCurve ModuleLineBundleTensorPullback LaurentPolynomial
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  originalStageToCompatibleProj ModuleSheafTensor.tensor divisorLineBundle
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "t" => parameter K 1
local notation "ρ" => algebraMap (Ring K 1) (ChartRing (t))
local notation "x" => leftCoordinate (t)
local notation "y" => rightCoordinate (t)
local notation "N₂" => completePointStagePoleTwoChartNumerator K n h 1 i i
local notation "N₃" => completePointStagePoleThreeChartNumerator K n h 1 i i
local notation "P₂" => leftLaurentMap (t) (N₂)
local notation "P₃" => leftLaurentMap (t) (N₃)
local notation "I₂" => AddMonoidAlgebra.coeff (precedingLaurentMap (Ring K 1) (t) (N₂)) (-1)
local notation "I₃" => AddMonoidAlgebra.coeff (precedingLaurentMap (Ring K 1) (t) (N₃)) (-1)

/-- The full original quadratic numerator retains its incoming linear coefficient. -/
theorem completePointFirstPoleTwo_node_polynomial :
    (N₂) = (ρ) ((P₂).coeff 2) + (ρ) ((P₂).coeff 1) * (x) +
      (ρ) ((P₂).coeff 2) * (x) ^ 2 + (ρ) (I₂) * (y) := by
  calc
    (N₂) = outgoingPolynomialLift (t) (P₂) +
        incomingPolynomialLift (t) (precedingLaurentMap (Ring K 1) (t) (N₂)) :=
      laurent_reconstruction (t) _
    _ = _ := by
      conv_lhs => rw [completePointFirstPoleTwo_polynomial K n h i]
      have h1 := outgoingPolynomialLift_monomial (t) ((P₂).coeff 1) 1
      have h2 := outgoingPolynomialLift_monomial (t) ((P₂).coeff 2) 2
      simp only [Nat.cast_one, Nat.cast_ofNat, pow_one] at h1 h2
      rw [outgoingPolynomialLift_add, outgoingPolynomialLift_add,
        outgoingPolynomialLift_constant,
        h1, h2,
        incomingPolynomialLift_linear (t) (precedingLaurentMap (Ring K 1) (t) (N₂))
          (completePointFirstNumerator_incoming_below K n h i 2
            (completePointStagePoleTwo K n h 1 i))]

/-- The full original cubic numerator retains all its lower terms and incoming coefficient. -/
theorem completePointFirstPoleThree_node_polynomial :
    (N₃) = -(ρ) ((P₃).coeff 3) + (ρ) ((P₃).coeff 1) * (x) +
      (ρ) ((P₃).coeff 2) * (x) ^ 2 + (ρ) ((P₃).coeff 3) * (x) ^ 3 +
      (ρ) (I₃) * (y) := by
  calc
    (N₃) = outgoingPolynomialLift (t) (P₃) +
        incomingPolynomialLift (t) (precedingLaurentMap (Ring K 1) (t) (N₃)) :=
      laurent_reconstruction (t) _
    _ = _ := by
      conv_lhs => rw [completePointFirstPoleThree_polynomial K n h i, ← map_neg]
      have h1 := outgoingPolynomialLift_monomial (t) ((P₃).coeff 1) 1
      have h2 := outgoingPolynomialLift_monomial (t) ((P₃).coeff 2) 2
      have h3 := outgoingPolynomialLift_monomial (t) ((P₃).coeff 3) 3
      simp only [Nat.cast_one, Nat.cast_ofNat, pow_one] at h1 h2 h3
      rw [outgoingPolynomialLift_add, outgoingPolynomialLift_add, outgoingPolynomialLift_add,
        outgoingPolynomialLift_constant, map_neg,
        h1, h2, h3,
        incomingPolynomialLift_linear (t) (precedingLaurentMap (Ring K 1) (t) (N₃))
          (completePointFirstNumerator_incoming_below K n h i 3
            (completePointStagePoleThree K n h 1 i))]

end FLT.Mazur.PolygonInfinitesimalStages
