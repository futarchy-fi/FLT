/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CurveGenericLineComparison
public import FLT.Mazur.FiniteSupportEulerCharacteristic
public import FLT.Mazur.CartierTensorRank
public import FLT.Mazur.TensorPowerDistribution

/-!
# Tensor degree of arbitrary lines on an integral proper curve

Two generic ideal comparisons reduce the tensor formula to the structure
sheaf; their finite-support errors cancel. No divisor presentation is assumed.
The tensor-power Euler characteristic follows by induction.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve

open ModuleSheafTensor ModuleLineBundleTensorPullback

variable {k : Type} [Field k] {X : Scheme} [IsIntegral X]
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
  (hd : topologicalKrullDim X ≤ 1)

include hd

/-- Euler characteristic of the tensor product of arbitrary lines on an integral curve. -/
theorem curveEulerCharacteristic_line_tensor {L N : X.Modules}
    (hL : LocallyFreeRankOne L) (hN : LocallyFreeRankOne N) :
    curveEulerCharacteristic f (tensor N L) =
      curveEulerCharacteristic f N + curveEulerCharacteristic f L -
        curveEulerCharacteristic f (structureModule X) := by
  have := Chow.source_isNoetherian f
  have := hN.isFinitePresentation
  have := (structureModule_locallyFreeRankOne (X := X)).isFinitePresentation
  obtain ⟨M, a, b, hM, ha, hb, hqa, hqb⟩ := exists_line_structure_comparison hd hN
  have h₁ := curveEulerCharacteristic_tensor_difference f a hqa hL
  have h₂ := curveEulerCharacteristic_tensor_difference f b hqb hL
  have hu : curveEulerCharacteristic f (tensor (structureModule X) L) =
      curveEulerCharacteristic f L := curveEulerCharacteristic_iso f (leftUnitor L)
  rw [hu] at h₁
  omega

/-- Cohomological degree is additive for arbitrary line sheaves on an integral proper curve. -/
theorem curveSheafDegree_line_tensor {L N : X.Modules}
    (hL : LocallyFreeRankOne L) (hN : LocallyFreeRankOne N) :
    curveSheafDegree f (tensor N L) = curveSheafDegree f N + curveSheafDegree f L := by
  unfold curveSheafDegree
  rw [curveEulerCharacteristic_line_tensor f hd hL hN]
  change _ = (curveEulerCharacteristic f N - curveEulerCharacteristic f (structureModule X)) +
    (curveEulerCharacteristic f L - curveEulerCharacteristic f (structureModule X))
  simp only [structureUnitModule, structureModule]
  ring

/-- Euler characteristic of every tensor power of an arbitrary line. -/
theorem curveEulerCharacteristic_line_power {L : X.Modules}
    (hL : LocallyFreeRankOne L) (n : ℕ) :
    curveEulerCharacteristic f (tensorPower L n) =
      (n : ℤ) * curveSheafDegree f L + curveEulerCharacteristic f (structureModule X) := by
  induction n with
  | zero => simp only [tensorPower, Nat.cast_zero, zero_mul, zero_add]
  | succ n ih =>
    change curveEulerCharacteristic f (tensor L (tensorPower L n)) = _
    rw [curveEulerCharacteristic_line_tensor f hd (hL.tensorPower n) hL, ih,
      Nat.cast_add, Nat.cast_one]
    change _ = (↑n + 1) *
      (curveEulerCharacteristic f L - curveEulerCharacteristic f (structureModule X)) + _
    simp only [curveSheafDegree, structureUnitModule, structureModule]
    ring

/-- Degree of an arbitrary line's tensor power is the exponent times its degree. -/
theorem curveSheafDegree_line_power {L : X.Modules}
    (hL : LocallyFreeRankOne L) (n : ℕ) :
    curveSheafDegree f (tensorPower L n) = (n : ℤ) * curveSheafDegree f L := by
  unfold curveSheafDegree at ⊢
  rw [curveEulerCharacteristic_line_power f hd hL n]
  exact add_sub_cancel_right _ _

end FLT.Mazur.FCurve
