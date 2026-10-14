/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeParameterUnits

/-!
# Evaluating original parameters and nonnegative labels

Primitive positive-depth witnesses evaluate both the global parameter and
the canonical natural representative of the component label. Midpoints
use the positive parameter and can also use the negative transition.
-/

@[expose] public noncomputable section
namespace FLT.Mazur
open IsLocalRing
variable {K : Type*} [Field K] {A : ValuationSubring K} {W : WeierstrassCurve A}
  {π : A} {n : ℕ} (D : SplitNodeDepth W π n) (c₆ : A)
  {P : (W.map (algebraMap A K)).toProjective.Point}

include D

/-- A bounded primitive witness of positive depth cannot have smooth reduction. -/
theorem NodePointCoordinates.not_smooth_of_positive
    (v : NodePointCoordinates A W π P) (hv0 : 0 < v.depth) (hv : v.depth ≤ n / 2) :
    ¬ SmoothReduction A W P := by
  intro hp
  have he := (nodePointLabel_eq_zero_iff D P).mpr hp
  rw [nodePointLabel_eq_of_coordinates D v,
    nodeBranchLabel_eq_zero_iff D.depth_pos hv] at he
  omega

/-- Positive branches and midpoints use their positive normalized parameter. -/
theorem nodePointParameter_positive (v : NodePointCoordinates A W π P)
    (hv0 : 0 < v.depth) (hv : v.depth ≤ n / 2)
    (hb : 2 * v.depth = n ∨ v.b ∈ maximalIdeal A) :
    nodePointParameter D c₆ P = nodePositiveParameter v := by
  classical
  rw [nodePointParameter_of_coordinates D c₆ v (v.not_smooth_of_positive D hv0 hv)]
  exact ite_eq_left hb

/-- Strict negative branches retain one original period coefficient. -/
theorem nodePointParameter_negative (v : NodePointCoordinates A W π P)
    (hv0 : 0 < v.depth) (hv : 2 * v.depth < n) (hb : IsUnit v.b) :
    nodePointParameter D c₆ P = nodeWrapParameter W c₆ * nodeNegativeParameter v := by
  classical
  rw [nodePointParameter_of_coordinates D c₆ v (v.not_smooth_of_positive D hv0 (by omega))]
  apply ite_eq_right
  rintro (h | h)
  · omega
  · exact h hb

/-- At the midpoint the negative convention has the same period factor. -/
theorem nodePointParameter_middle_negative (h6 : W.a₆ = π ^ n * c₆)
    (v : NodePointCoordinates A W π P) (hm : 2 * v.depth = n) :
    nodePointParameter D c₆ P = nodeWrapParameter W c₆ * nodeNegativeParameter v := by
  rw [nodePointParameter_positive D c₆ v (by have := D.depth_pos; omega)
    (by omega) (Or.inl hm)]
  exact node_middle_parameter_transition D v hm c₆ h6

/-- The nonnegative label of a positive branch or midpoint is its actual depth. -/
theorem nodePointLabel_val_positive (v : NodePointCoordinates A W π P)
    (hv : v.depth ≤ n / 2) (hb : 2 * v.depth = n ∨ v.b ∈ maximalIdeal A) :
    (nodePointLabel D P).val = v.depth := by
  classical
  rw [nodePointLabel_eq_of_coordinates D v]
  have he : nodeBranchLabel n v.depth v.b = (v.depth : ZMod n) := ite_eq_left hb
  rw [he, ZMod.val_natCast, Nat.mod_eq_of_lt (by have := D.depth_pos; omega)]

/-- The nonnegative label of a strict negative branch is the complementary depth. -/
theorem nodePointLabel_val_negative (v : NodePointCoordinates A W π P)
    (hv0 : 0 < v.depth) (hv : 2 * v.depth < n) (hb : IsUnit v.b) :
    (nodePointLabel D P).val = n - v.depth := by
  have hn := D.depth_pos
  have he : -(v.depth : ZMod n) = ((n - v.depth : ℕ) : ZMod n) := by
    rw [Nat.cast_sub (by omega : v.depth ≤ n), ZMod.natCast_self, zero_sub]
  rw [nodePointLabel_eq_of_coordinates D v, nodeBranchLabel_eq_neg_of_unit n v.depth hb,
    he, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]

/-- The canonical representatives cross at most one full component period. -/
def nodePointCarry (P Q : (W.map (algebraMap A K)).toProjective.Point) : ℕ :=
  if n ≤ (nodePointLabel D P).val + (nodePointLabel D Q).val then 1 else 0

/-- The carry is symmetric in the actual input points. -/
theorem nodePointCarry_comm (P Q : (W.map (algebraMap A K)).toProjective.Point) :
    nodePointCarry D P Q = nodePointCarry D Q P := by
  simp only [nodePointCarry, Nat.add_comm]

end FLT.Mazur
