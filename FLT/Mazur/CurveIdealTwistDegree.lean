/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CurveLineTensorDegree

/-!
# Euler characteristic of ideal twists of arbitrary line powers

A nonzero ideal embeds into the structure sheaf with finite-support cokernel.
The finite-support tensor comparison therefore computes the Euler characteristic
of every ideal twist, without requiring the ideal to be invertible.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve

open ModuleSheafTensor ModuleLineBundleTensorPullback
open CoherentDevissage FLT.Mazur.CoherentIdealIntersection

variable {k : Type} [Field k] {X : Scheme} [IsIntegral X]
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
  (hd : topologicalKrullDim X ≤ 1)

include hd in
/-- Nonzero ideal twists have the same Euler-characteristic slope as the original line. -/
theorem curveEulerCharacteristic_ideal_line_power (I : X.IdealSheafData) (hI : I ≠ ⊥)
    {L : X.Modules} (hL : LocallyFreeRankOne L) (n : ℕ) :
    curveEulerCharacteristic f (tensor (idealModule I) (tensorPower L n)) =
      (n : ℤ) * curveSheafDegree f L + curveEulerCharacteristic f (idealModule I) := by
  have := Chow.source_isNoetherian f
  have := idealModule_coherent I
  have := (structureModule_locallyFreeRankOne (X := X)).isFinitePresentation
  have := idealModuleι_stalk_isIso I (genericPoint X) (genericPoint_notMem_zeroLocus I hI)
  have hs := finite_cokernel_support_of_generic_isIso hd (idealModuleι I)
  have h := curveEulerCharacteristic_tensor_difference f (idealModuleι I) hs (hL.tensorPower n)
  have hu : curveEulerCharacteristic f (tensor (structureModule X) (tensorPower L n)) =
      curveEulerCharacteristic f (tensorPower L n) :=
    curveEulerCharacteristic_iso f (leftUnitor _)
  rw [hu, curveEulerCharacteristic_line_power f hd hL n] at h
  omega

end FLT.Mazur.FCurve
