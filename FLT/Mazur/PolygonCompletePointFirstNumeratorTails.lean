/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointNumeratorParameterTails

/-!
# The first-stage retained Laurent numerator with explicit end terms

The middle degree interval keeps its original coefficients. The two outer
terms are explicitly the parameter times the original adjacent branch
coefficients; no normalization of the complete lifts is performed.
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
local notation "L" => originalStageSinglePointLine K n h 1 i
local notation "N" => completePointStageChartNumerator K n h 1 i
local notation "p" => Equiv.symm (finRotate n) i

/-- The exact first-order Laurent form retains the central polynomial and both parameter tails. -/
theorem completePointFirstNumerator_parameter_expansion (d : ℕ)
    (s : Γ(tensorPower (L) d, ⊤)) :
    leftLaurentMap (t) (N i d s) =
      C ((t) * (precedingLaurentMap (Ring K 1) (t) (N i d s)).coeff (-1)) * T (-1) +
      C ((-1 : Ring K 1) ^ d * (t) *
        (leftLaurentMap (t) (N (p) d s)).coeff 1) * T ((d : ℤ) + 1) +
      ∑ k ∈ Finset.Icc (0 : ℤ) d,
        C ((leftLaurentMap (t) (N i d s)).coeff k) * T k := by
  have hI : Finset.Icc (-1 : ℤ) ((d : ℤ) + 1) =
      insert (-1) (insert ((d : ℤ) + 1) (Finset.Icc (0 : ℤ) d)) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  conv_lhs => rw [completePointStageNumerator_expansion K n h 1 i d s]
  change (∑ k ∈ Finset.Icc (-1 : ℤ) ((d : ℤ) + 1), _) = _
  rw [hI, Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_Icc]; omega),
    Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
  have hl := completePointStageNumerator_lower_parameter K n h 1 i d s 1
  have hu := completePointStageNumerator_upper_parameter K n h 1 i d s 1
  simp only [pow_one, Nat.cast_one, add_comm (1 : ℤ)] at hl hu
  rw [hl, hu, add_assoc]

end FLT.Mazur.PolygonInfinitesimalStages
