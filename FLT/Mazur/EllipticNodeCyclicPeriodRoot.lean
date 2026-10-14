/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeLabelHom
public import FLT.Mazur.EllipticNodeParameterMultiples

/-!
# A cyclic original marking selects the period root

An actual generic n-torsion point on component one supplies a root of the
original period through its original parameter. Trivialization by that root
makes every translation by the cyclic marking preserve the torus coordinate.
This is an arithmetic statement about actual original points.
-/

@[expose] public noncomputable section
namespace FLT.Mazur
open IsLocalRing
variable {K : Type*} [Field K] {A : ValuationSubring K} {W : WeierstrassCurve A}
  {π : A} {n : ℕ} (D : SplitNodeDepth W π n) (c₆ : A) (h6 : W.a₆ = π ^ n * c₆)
  (T : (W.map (algebraMap A K)).toProjective.Point)
  (hlabel : (nodePointLabel D T).val = 1) (hT : n • T = 0)

include hlabel hT in
/-- The parameter of an actual cyclic marking on component one is a period root. -/
theorem nodeCyclicMarking_period_root :
    nodePointParameterUnit D c₆ h6 T ^ n = nodeWrapParameterUnit D c₆ h6 := by
  have he := nodePointParameterUnit_pow_period D c₆ h6 T
  simpa only [hlabel, hT, pow_one, nodePointParameterUnit_zero, mul_one] using he

include hlabel in
/-- Trivialization by the marking parameter sends that same marking to the torus identity. -/
theorem nodeCyclicMarking_trivialized_self :
    nodeTrivializedParameter D c₆ h6 (nodePointParameterUnit D c₆ h6 T) T = 1 := by
  simp only [nodeTrivializedParameter, hlabel, pow_one, div_self']

include hlabel hT in
/-- Every natural multiple of the cyclic marking has trivial torus coordinate. -/
theorem nodeCyclicMarking_trivialized_nsmul (m : ℕ) :
    nodeTrivializedParameter D c₆ h6 (nodePointParameterUnit D c₆ h6 T) (m • T) = 1 := by
  let f := nodeTrivializedParameterHom D c₆ h6 (nodePointParameterUnit D c₆ h6 T)
    (nodeCyclicMarking_period_root D c₆ h6 T hlabel hT)
  have hz : f T = 0 := congrArg Additive.ofMul
    (nodeCyclicMarking_trivialized_self D c₆ h6 T hlabel)
  have he := f.map_nsmul m T
  rw [hz, nsmul_zero] at he
  exact congrArg Additive.toMul he

include hlabel hT in
/-- Translation by any actual cyclic marking leaves the trivialized torus coordinate unchanged. -/
theorem nodeCyclicMarking_trivialized_translate
    (P : (W.map (algebraMap A K)).toProjective.Point) (m : ℕ) :
    nodeTrivializedParameter D c₆ h6 (nodePointParameterUnit D c₆ h6 T) (P + m • T) =
      nodeTrivializedParameter D c₆ h6 (nodePointParameterUnit D c₆ h6 T) P := by
  rw [nodeTrivializedParameter_add D c₆ h6 _
    (nodeCyclicMarking_period_root D c₆ h6 T hlabel hT),
    nodeCyclicMarking_trivialized_nsmul D c₆ h6 T hlabel hT m, mul_one]

include hlabel in
/-- The label of the actual cyclic translation increases by its integer marking index. -/
theorem nodeCyclicMarking_label_translate
    (P : (W.map (algebraMap A K)).toProjective.Point) (m : ℕ) :
    nodePointLabel D (P + m • T) = nodePointLabel D P + (m : ZMod n) := by
  have : NeZero n := ⟨Nat.ne_of_gt D.depth_pos⟩
  have hl : nodePointLabel D T = 1 := by
    rw [← ZMod.natCast_zmod_val (nodePointLabel D T), hlabel, Nat.cast_one]
  change nodePointLabelHom D (P + m • T) = _
  rw [map_add, map_nsmul, nodePointLabelHom_apply, nodePointLabelHom_apply, hl,
    nsmul_eq_mul, mul_one]

end FLT.Mazur
