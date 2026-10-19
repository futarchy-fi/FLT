/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluInfinityEvaluationIdeal
public import FLT.FreyCurve.Serre.VeluInfinityTargetOpen
public import FLT.Mazur.LocalizationEvaluationKernel

/-!
# The identity ideal on the actual Vélu infinity neighborhood

The successive original denominator localizations preserve the principal
ideal of the source identity. The generator remains the original u-coordinate.
-/

@[expose] public noncomputable section

open FLT.Mazur.WeierstrassIntegralChart FLT.Mazur.LocalizationEvaluationKernel

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type} [Field K] [DecidableEq K]
  (E : WeierstrassCurve K) (G : AddSubgroup E.toAffine.Point) [Fintype G]

/-- The full identity ideal on the original denominator neighborhood is still (u). -/
theorem infinityKernelEvaluation_ker :
    RingHom.ker (infinityKernelEvaluation E G).toRingHom = Ideal.span {infinityU E G} :=
  ker_eq_span (Submonoid.powers (infinityKernelDenominator E G))
    (infinityParameterEvaluation E).toRingHom (infinityKernelEvaluation E G).toRingHom
    (infinityKernelEvaluation_algebraMap E G) _ (infinityParameterEvaluation_ker E)

variable [CharZero K]

/-- The original parameter on the normalized target-chart neighborhood. -/
def infinityTargetU : InfinityTargetRing E G :=
  algebraMap (InfinityKernelRing E G) _ (infinityU E G)

/-- The original identity is cut out by u on the actual source of the target chart map. -/
theorem infinityTargetEvaluation_ker :
    RingHom.ker (infinityTargetEvaluation E G).toRingHom = Ideal.span {infinityTargetU E G} :=
  ker_eq_span (Submonoid.powers (infinityScaledY E G))
    (infinityKernelEvaluation E G).toRingHom (infinityTargetEvaluation E G).toRingHom
    (infinityTargetEvaluation_algebraMap E G) _ (infinityKernelEvaluation_ker E G)

end WeierstrassCurve.Velu
