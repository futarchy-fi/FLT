/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.BlowupReesRatioRight
public import FLT.Mazur.BlowupReesZeroComponent
public import FLT.Mazur.BlowupFractionChartExt

/-!
# Original functions on both sides of a Rees ratio intersection

The two product-chart comparisons agree on the original coefficient ring.
The numerator and denominator remain regular on each full ratio open.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.BlowupRees

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {A : Type*} [CommRing A] (I : Ideal A) (f : A) (hf : f ∈ I)
  (a : A) (ha : a ∈ I)

/-- Original functions restricted to the full fraction ratio open. -/
def originalOnRatio : A →+* FractionRatioOpen I f a ha :=
  (algebraMap (BlowupFractionChart.chart I f) _).comp
    (algebraMap A (BlowupFractionChart.chart I f))

/-- Original functions in the common product-generator homogeneous chart. -/
def originalOnProduct : A →+* ProductChart I f hf a ha :=
  (HomogeneousLocalization.fromZeroRingHom (component I) _).comp (originalToZero I)

/-- The first ratio comparison retains every original function. -/
@[simp] theorem fractionRatioEquiv_original (z : A) :
    fractionRatioEquiv I f hf a ha (originalOnRatio I f a ha z) =
      originalOnProduct I f hf a ha z := by
  rw [originalOnRatio, RingHom.comp_apply]
  rw [fractionRatioEquiv_base, ← degreeZeroEquiv_original I f hf z,
    RingEquiv.symm_apply_apply]
  exact HomogeneousLocalization.awayMap_fromZeroRingHom _ _ _ _

/-- The second ratio comparison retains the same original function. -/
@[simp] theorem rightFractionRatioEquiv_original (z : A) :
    rightFractionRatioEquiv I f hf a ha (originalOnRatio I a f hf z) =
      originalOnProduct I f hf a ha z := by
  rw [originalOnRatio, RingHom.comp_apply]
  rw [rightFractionRatioEquiv_base, ← degreeZeroEquiv_original I a ha z,
    RingEquiv.symm_apply_apply]
  exact HomogeneousLocalization.awayMap_fromZeroRingHom _ _ _ _

/-- The original denominator remains regular on the entire ratio open. -/
theorem originalOnRatio_denominator_regular : IsRegular (originalOnRatio I f a ha f) :=
  BlowupFractionChart.localized_denominator_regular I f
    (Submonoid.powers (BlowupFractionChart.ratio I f a ha)) (FractionRatioOpen I f a ha)

/-- The original numerator also stays regular, since its ratio is now a unit. -/
theorem originalOnRatio_numerator_regular : IsRegular (originalOnRatio I f a ha a) := by
  have he := congrArg (algebraMap (BlowupFractionChart.chart I f) (FractionRatioOpen I f a ha))
    (BlowupFractionChart.denominator_mul_ratio I f a ha)
  rw [map_mul] at he
  rw [originalOnRatio, RingHom.comp_apply, ← he]
  exact (originalOnRatio_denominator_regular I f a ha).mul
    (IsLocalization.Away.algebraMap_isUnit (BlowupFractionChart.ratio I f a ha)).isRegular

end FLT.Mazur.BlowupRees
