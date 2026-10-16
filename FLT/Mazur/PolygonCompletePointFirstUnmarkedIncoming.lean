/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointFirstIncomingTail

/-!
# Incoming coefficients beyond the two marked charts

An unmarked chart has parameter-annihilated negative incoming coefficients.
Consequently the marked chart has no incoming negative coefficient unless
its successor is also its predecessor, the two-cycle case.
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

/-- The next original edge kills parameter times every unmarked incoming negative coefficient. -/
theorem completePointFirstNumerator_unmarked_parameter_incoming
    (j : Fin n) (hji : j ≠ i) (hjp : j ≠ (p))
    (d : ℕ) (s : Γ(tensorPower (L) d, ⊤)) (k : ℤ) (hk : k < 0) :
    (t) * (precedingLaurentMap (Ring K 1) (t) (N j d s)).coeff k = 0 := by
  let l := finRotate n j
  have hl : (finRotate n).symm l = j := Equiv.symm_apply_apply _ _
  have hli : l ≠ i := fun he ↦ hjp (hl.symm.trans (congrArg (finRotate n).symm he))
  have he := completePointStageChartNumerator_laurent K n h 1 i l d s
  rw [hl] at he
  have hz := parameter_leftLaurentMap_negative (t) (parameter_pow K 1) (N l d s) k hk
  by_cases hlp : l = (p)
  · have he' : (C (t) * T (-1) - 1) ^ d *
        precedingLaurentMap (Ring K 1) (t) (N j d s) = leftLaurentMap (t) (N l d s) := by
      simpa only [PolygonInfinitesimal.chartMarkingEquation, ite_eq_right hli, ite_eq_left hlp,
        ite_eq_right hji, ite_eq_right hjp, inv_one, Units.val_one, map_sub, map_one,
        leftLaurentMap_right, one_pow, one_mul] using he
    have hh := congrArg (fun z ↦ C (t) * z) he'
    rw [LaurentSquareZeroMarking.parameter_marking_pow_mul (t) (parameter_pow K 1)] at hh
    have hc := congrArg (fun z : (Ring K 1)[T;T⁻¹] ↦ z.coeff k) hh
    simp only [← single_eq_C, AddMonoidAlgebra.coeff_single_mul_apply,
      neg_zero, zero_add] at hc
    apply (((isUnit_one : IsUnit (1 : Ring K 1)).neg).pow d).isRegular.left
    dsimp only
    rw [mul_zero, ← mul_assoc, mul_comm ((-1 : Ring K 1) ^ d) (t), hc, hz]
  · have he' : precedingLaurentMap (Ring K 1) (t) (N j d s) =
        leftLaurentMap (t) (N l d s) := by
      simpa only [PolygonInfinitesimal.chartMarkingEquation, hli, hlp, hji, hjp,
        ite_false, map_one, one_pow, one_mul] using he
    rw [he']
    exact hz

/-- With an unmarked successor, the retained incoming coefficient itself is zero. -/
theorem completePointFirstNumerator_incoming_of_not_twoCycle
    (hcycle : (finRotate n).symm ((finRotate n).symm i) ≠ i)
    (d : ℕ) (s : Γ(tensorPower (L) d, ⊤)) :
    (precedingLaurentMap (Ring K 1) (t) (N i d s)).coeff (-1) = 0 := by
  let j := finRotate n i
  have hj : (finRotate n).symm j = i := Equiv.symm_apply_apply _ _
  have hji : j ≠ i := by
    intro he
    exact PolygonCyclicAtlas.prev_ne h i (he ▸ hj)
  have hjp : j ≠ (p) := fun he ↦ hcycle (he ▸ hj)
  rw [completePointFirstNumerator_next_negative K n h i j hj hji hjp,
    show (-1 : ℤ) = -(1 : ℕ) by rfl, branch_coefficient_nonpos, pow_one, Nat.cast_one,
    completePointFirstNumerator_unmarked_parameter_incoming K n h i j hji hjp d s
      (-1) (by decide), mul_zero]

end FLT.Mazur.PolygonInfinitesimalStages
