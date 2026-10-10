/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.BlowupFractionChartLocalization

/-!
# Actual generator ratios in Rees fraction charts

These elements specify the principal opens used for transitions. Their
incidence relation retains the original center generator and denominator.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.BlowupFractionChart

variable {A : Type*} [CommRing A] (I : Ideal A) (f : A)

/-- A center element divided by the chart denominator, inside the Rees image. -/
def ratio (a : A) (ha : a ∈ I) : chart I f :=
  ⟨algebraMap A (Localization.Away f) a * IsLocalization.Away.invSelf f, by
    rw [chart_eq_adjoin]
    exact Algebra.subset_adjoin ⟨a, ha, rfl⟩⟩

/-- The ratio is represented by the actual original fraction. -/
@[simp] theorem ratio_val (a : A) (ha : a ∈ I) :
    (ratio I f a ha : Localization.Away f) =
      algebraMap A (Localization.Away f) a * IsLocalization.Away.invSelf f := rfl

/-- Multiplying the ratio by its original denominator recovers the center element. -/
theorem denominator_mul_ratio (a : A) (ha : a ∈ I) :
    denominator I f * ratio I f a ha = algebraMap A (chart I f) a := by
  apply Subtype.ext
  change algebraMap A (Localization.Away f) f *
    (algebraMap A (Localization.Away f) a * IsLocalization.Away.invSelf f) = _
  rw [mul_left_comm, IsLocalization.Away.mul_invSelf, mul_one]
  rfl

/-- The chart denominator is regular even when the original ring has zero divisors. -/
theorem denominator_regular : IsRegular (denominator I f) := by
  have hu : IsRegular (algebraMap A (Localization.Away f) f) :=
    (IsLocalization.Away.algebraMap_isUnit f).isRegular
  constructor
  · intro a b h
    apply Subtype.ext
    apply hu.left
    exact congrArg (fun z : chart I f => (z : Localization.Away f)) h
  · intro a b h
    apply Subtype.ext
    apply hu.right
    exact congrArg (fun z : chart I f => (z : Localization.Away f)) h

/-- The self-ratio is one, so it contributes no extra generator to the chart. -/
@[simp] theorem ratio_self (hf : f ∈ I) : ratio I f f hf = 1 := by
  apply Subtype.ext
  exact IsLocalization.Away.mul_invSelf f

end FLT.Mazur.BlowupFractionChart
