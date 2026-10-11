/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.BlowupFractionChartMap
public import FLT.Mazur.BlowupFractionChartExt

/-!
# Lifting into a regular principalized center

A fraction chart of a principal ideal is the original ring when its generator
is regular. Consequently any coefficient map making the center divisible by
a regular image denominator extends uniquely to the original fraction chart.
This also applies to actual flat base changes of modification charts.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.BlowupFractionChart

set_option backward.isDefEq.respectTransparency false

variable {A : Type*} [CommRing A]

/-- A principal-center fraction chart contains only original coefficients. -/
theorem principal_chart_eq_bot (f : A) : chart (Ideal.span {f}) f = ⊥ := by
  rw [chart_span]
  apply le_antisymm _ bot_le
  apply Algebra.adjoin_le
  rintro _ ⟨a, ha, rfl⟩
  obtain rfl := Set.mem_singleton_iff.mp ha
  dsimp only
  rw [denominator_ratio]
  exact Subalgebra.one_mem _

/-- Regularity ensures no original coefficient is lost in the principal fraction chart. -/
def principalChartEquiv (f : A) (hf : IsRegular f) :
    A ≃ₐ[A] chart (Ideal.span {f}) f :=
  AlgEquiv.ofBijective (Algebra.ofId A _) (by
    constructor
    · intro a b h
      have hi : Function.Injective (algebraMap A (Localization.Away f)) := by
        apply (IsLocalization.injective_iff_isRegular (Submonoid.powers f)).mpr
        rintro ⟨x, ⟨n, rfl⟩⟩
        exact hf.pow n
      exact hi (congrArg Subtype.val h)
    · intro z
      have hz : (z : Localization.Away f) ∈ (⊥ : Subalgebra A (Localization.Away f)) :=
        principal_chart_eq_bot f ▸ z.property
      obtain ⟨a, ha⟩ := Algebra.mem_bot.mp hz
      exact ⟨a, Subtype.ext ha⟩)

/-- The principal chart comparison is the original coefficient map. -/
@[simp] theorem principalChartEquiv_apply (f : A) (hf : IsRegular f) (a : A) :
    principalChartEquiv f hf a = algebraMap A _ a := rfl

variable {B : Type*} [CommRing B] (I : Ideal A) (φ : A →+* B) (f : A)
  (hI : I.map φ ≤ Ideal.span {φ f}) (hf : IsRegular (φ f))

/-- A regular image denominator dividing the entire center gives an actual chart lift. -/
irreducible_def principalLift : chart I f →+* B :=
  (principalChartEquiv (φ f) hf).symm.toRingHom.comp
    (chartMap I (Ideal.span {φ f}) φ hI f)

/-- The constructed lift preserves every original coefficient. -/
@[simp] theorem principalLift_base (a : A) :
    principalLift I φ f hI hf (algebraMap A _ a) = φ a := by
  rw [principalLift_def, RingHom.comp_apply, chartMap_base]
  exact (principalChartEquiv (φ f) hf).symm_apply_apply (φ a)

/-- Lifted ratios solve their original numerator equations. -/
theorem principalLift_ratio (a : A) (ha : a ∈ I) :
    φ f * principalLift I φ f hI hf (ratio I f a ha) = φ a := by
  rw [← principalLift_base I φ f hI hf f, ← map_mul]
  change principalLift I φ f hI hf (denominator I f * ratio I f a ha) = _
  rw [denominator_mul_ratio, principalLift_base]

/-- Regularity makes this extension unique among maps retaining the original coefficients. -/
theorem principalLift_unique (k : chart I f →+* B)
    (hk : ∀ a, k (algebraMap A _ a) = φ a) : k = principalLift I φ f hI hf := by
  apply ringHom_ext_of_denominator_regular I f k _
  · ext a
    exact (hk a).trans (principalLift_base I φ f hI hf a).symm
  · change IsRegular (k (algebraMap A _ f))
    rwa [hk]

end FLT.Mazur.BlowupFractionChart
