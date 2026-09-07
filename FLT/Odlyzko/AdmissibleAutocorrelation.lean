/-
Copyright (c) 2026 Kelly Azevedo Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelly Azevedo Santos
-/
module

public import FLT.AINTLIB.DedekindResidue.ExplicitFormula.TestFunction
public import FLT.Odlyzko.Autocorrelation

/-!
# Admissibility of autocorrelation test functions

The theorem below separates the structural input supplied by autocorrelation from the two
one-dimensional bounded-variation estimates needed by the Weil--Poitou formula.  The derivative
witnesses are explicit: a concrete Tartar function can discharge them without hiding any extra
regularity assumption.
-/

@[expose] public section

open MeasureTheory

namespace Odlyzko

/-- The exponentially weighted autocorrelation occurring in the admissibility condition. -/
noncomputable def weightedAutocorrelation (g : ℝ → ℝ) (epsilon : ℝ) : ℝ → ℂ :=
  fun x ↦ autocorrelation g x * ((Real.exp ((1 / 2 + epsilon) * x) : ℝ) : ℂ)

/-- The difference quotient occurring in the admissibility condition. -/
noncomputable def autocorrelationDiffQuot (g : ℝ → ℝ) : ℝ → ℂ :=
  fun x ↦ (autocorrelation g 0 - autocorrelation g x) / x

/--
An autocorrelation is admissible once the two analytic derivative estimates are supplied.

The `LipschitzWith` hypothesis records the regularity required of the eventual concrete input.
For a general abstract Lipschitz function, bounded variation of the difference quotient does not
follow formally without an additional derivative estimate, so that estimate is exposed rather
than silently assumed.
-/
theorem autocorrelation_isAdmissibleTestFn (g : ℝ → ℝ) (C : NNReal)
    (hg_even : Function.Even g) (hg_cont : Continuous g) (hg_compact : HasCompactSupport g)
    (_hg_lipschitz : LipschitzWith C g) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (weightedDeriv quotientDeriv : ℝ → ℂ)
    (hweighted_deriv : ∀ x ∈ Set.Ioi 0,
      HasDerivAt (weightedAutocorrelation g epsilon) (weightedDeriv x) x)
    (hweighted_integrable : IntegrableOn weightedDeriv (Set.Ici 0))
    (hweighted_fn_integrable : IntegrableOn (weightedAutocorrelation g epsilon) (Set.Ici 0))
    (hquotient_cont : ContinuousOn (autocorrelationDiffQuot g) (Set.Ici 0))
    (hquotient_deriv : ∀ x ∈ Set.Ioi 0,
      HasDerivAt (autocorrelationDiffQuot g) (quotientDeriv x) x)
    (hquotient_integrable : IntegrableOn quotientDeriv (Set.Ici 0)) :
    DedekindResidue.IsAdmissibleTestFn (autocorrelation g) := by
  have hF_cont : Continuous (autocorrelation g) :=
    continuous_autocorrelation g hg_cont hg_compact
  have hweighted_cont : ContinuousOn (weightedAutocorrelation g epsilon) (Set.Ici 0) := by
    apply Continuous.continuousOn
    have hexp : Continuous (fun x : ℝ ↦ Real.exp ((1 / 2 + epsilon) * x)) := by
      fun_prop
    exact hF_cont.mul (Complex.continuous_ofReal.comp hexp)
  have hweighted_bv :
      BoundedVariationOn (weightedAutocorrelation g epsilon) (Set.Ici 0) := by
    apply DedekindResidue.boundedVariationOn_of_deriv_integrable Set.ordConnected_Ici
      hweighted_cont
    · simpa only [interior_Ici] using hweighted_deriv
    · exact hweighted_integrable
  have hquotient_bv : BoundedVariationOn (autocorrelationDiffQuot g) (Set.Ici 0) := by
    apply DedekindResidue.boundedVariationOn_of_deriv_integrable Set.ordConnected_Ici
      hquotient_cont
    · simpa only [interior_Ici] using hquotient_deriv
    · exact hquotient_integrable
  refine ⟨autocorrelation_even g hg_even, ⟨epsilon, hepsilon, ?_, ?_⟩, ?_, ?_⟩
  · exact hweighted_bv
  · exact hweighted_fn_integrable
  · exact hquotient_bv
  · intro x
    refine ⟨autocorrelation g x, autocorrelation g x, ?_, ?_, by ring⟩
    · exact hF_cont.continuousAt.mono_left inf_le_left
    · exact hF_cont.continuousAt.mono_left inf_le_left

end Odlyzko
