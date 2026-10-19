/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluInfinityLinearFactor
public import FLT.FreyCurve.Serre.VeluInfinityNeighborhoodIdeal
public import FLT.Mazur.SealedPrincipalLocalization

/-!
# The sealed coordinate ring of the simple infinity neighborhood

Invert the explicit linear factor after normalizing the target chart.
The original identity lifts to this neighborhood and its full ideal is (u).
-/

@[expose] public noncomputable section

open FLT.Mazur.WeierstrassIntegralChart FLT.Mazur.LocalizationEvaluationKernel

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] infinityTargetCoordinates infinityTargetChart

variable {K : Type} [Field K] [CharZero K] [DecidableEq K]
  (E : WeierstrassCurve K) (G : AddSubgroup E.toAffine.Point) [Fintype G]

/-- The original linear factor on the normalized target-chart neighborhood. -/
def infinityTargetXFactor : InfinityTargetRing E G :=
  algebraMap (InfinityKernelRing E G) _ (infinityXFactor E G)

/-- The factor being inverted still has value one at the original identity. -/
@[simp] theorem infinityTargetXFactor_value :
    infinityTargetEvaluation E G (infinityTargetXFactor E G) = 1 := by
  simp [infinityTargetXFactor]

/-- An actual principal neighborhood on which the original target parameter is simple. -/
abbrev InfinitySimpleRing :=
  FLT.Mazur.SealedPrincipalLocalization.Ring (infinityTargetXFactor E G)

end WeierstrassCurve.Velu
