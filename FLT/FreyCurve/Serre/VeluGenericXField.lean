/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluGenericChartMorphism
public import Mathlib.FieldTheory.RatFunc.IntermediateField

/-!
# The original generic Vélu x-coordinate is transcendental

The pole estimate excludes constants. Consequently the actual target x-line
embeds into the source function field by substitution of the original Vélu
function. This supplies the x-coordinate part of the function-field map.
-/

@[expose] public noncomputable section

open scoped Polynomial
open RatFunc

namespace WeierstrassCurve.Velu

variable {K : Type} [Field K] [CharZero K] [DecidableEq K]
  (E : WeierstrassCurve K) (G : AddSubgroup E.toAffine.Point) [Fintype G]

omit [CharZero K] in
/-- The original rational Vélu x function is transcendental over the coefficient field. -/
theorem xFunction_transcendental : Transcendental K (xFunction E G) := by
  apply RatFunc.transcendental_of_ne_C
  rintro ⟨c, hc⟩
  exact xFunction_sub_C_not_degreeLE E G c (Or.inl (sub_eq_zero.mpr hc))

/-- The exact lifted x-coordinate remains transcendental in the quadratic source field. -/
theorem veluGenericX_transcendental : Transcendental K (liftX E (xFunction E G)) := by
  apply (transcendental_algebraMap_iff
    (algebraMap K⟮X⟯ (FunctionField E)).injective).mpr
  exact xFunction_transcendental E G

/-- Substitute the original generic Vélu x-coordinate into the target rational x-line. -/
def veluGenericXFieldHom : K⟮X⟯ →ₐ[K] FunctionField E :=
  (IntermediateField.adjoin K {liftX E (xFunction E G)}).val.comp
    (RatFunc.algEquivOfTranscendental (liftX E (xFunction E G))
      (veluGenericX_transcendental E G)).toAlgHom

/-- The target x variable maps to the original x function, not a chosen substitute. -/
@[simp] theorem veluGenericXFieldHom_X :
    veluGenericXFieldHom E G RatFunc.X = liftX E (xFunction E G) :=
  RatFunc.algEquivOfTranscendental_X _ _

/-- This actual map of x-function fields is injective. -/
theorem veluGenericXFieldHom_injective : Function.Injective (veluGenericXFieldHom E G) :=
  (veluGenericXFieldHom E G).injective

end WeierstrassCurve.Velu
