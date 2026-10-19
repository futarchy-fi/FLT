/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluGlobalKernelCover
public import FLT.Mazur.FiniteUnramifiedFieldLength

/-!
# The full original Vélu kernel is finite etale and reduced

The original subgroup sections form an actual open cover on which the
structure map is the identity. These are properties of the full pullback.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type} [Field K] [CharZero K] [IsAlgClosed K] [DecidableEq K]
  (E : WeierstrassCurve K) [E.IsElliptic]
  (G : AddSubgroup E.toAffine.Point) [Fintype G]
  (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q)

/-- The actual full kernel structure morphism is etale over the original field. -/
instance veluGlobalKernel_etale :
    Etale (pullback.snd (veluGlobalMorphism E G hodd) (integralCurveZero (curve E G))) := by
  apply IsZariskiLocalAtSource.of_openCover (P := @Etale)
    (veluGlobalKernelOpenCover E G hodd)
  intro P
  change Etale (veluGlobalKernelPoint E G hodd P ≫ pullback.snd _ _)
  rw [veluGlobalKernelPoint_snd]
  infer_instance

/-- The full original fiber has no nilpotents anywhere. -/
instance veluGlobalKernel_reduced : IsReduced (veluGlobalKernel E G hodd) :=
  FLT.Mazur.FCurve.finiteUnramifiedField_reduced
    (pullback.snd (veluGlobalMorphism E G hodd) (integralCurveZero (curve E G)))

/-- Its actual algebraic length equals its number of scheme points. -/
theorem veluGlobalKernel_length_eq_card :
    FLT.Mazur.FCurve.finiteSchemeLength
      (pullback.snd (veluGlobalMorphism E G hodd) (integralCurveZero (curve E G))) =
        Nat.card (veluGlobalKernel E G hodd) :=
  FLT.Mazur.FCurve.finiteUnramifiedField_length_eq_card _

end WeierstrassCurve.Velu
