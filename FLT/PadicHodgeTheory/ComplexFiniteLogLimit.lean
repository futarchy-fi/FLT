/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexCyclotomicPowerConvergence
public import FLT.PadicHodgeTheory.ComplexFiniteLogEvaluation
public import FLT.PadicHodgeTheory.FiniteLogContinuity
public import FLT.PadicHodgeTheory.PadicResidueConvergence

/-! # Cyclotomic logarithm limits at every actual finite theta level -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- The actual cyclotomic integer approximants converge through the existing scalar map. -/
theorem complexCyclotomicExponent_tendsto_finite (σ : PadicGalois p) (r : ℕ) :
    Filter.Tendsto (fun n ↦ (complexCyclotomicExponent p σ n : ComplexFiniteThetaQuotient p r))
      Filter.atTop (nhds (complexFiniteThetaQuotientScalars p r
        ((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv).val : ℚ_[p]))) := by
  have h := (complexFiniteThetaQuotientScalars_continuous p r).continuousAt.tendsto.comp
    (padicResidue_tendsto_rational p
      (cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv).val)
  simpa only [Function.comp_def, map_natCast, complexCyclotomicExponent] using h

/-- The existing completed argument has exactly the required natural-power limit. -/
theorem complexCyclotomicArgument_pow_tendsto (σ : PadicGalois p) (r : ℕ) :
    Filter.Tendsto (fun n ↦
      (1 + complexDeRhamFiniteEval p r (complexCyclotomicArgument p)) ^
        complexCyclotomicExponent p σ n) Filter.atTop
      (nhds (1 + complexDeRhamFiniteEval p r
        (complexDeRhamGalois p σ (complexCyclotomicArgument p)))) := by
  simpa only [complexCyclotomicArgument_eval, complexCyclotomicArgument_galois_eval,
    ← add_sub_assoc, add_sub_cancel_left] using complexCyclotomicPower_tendsto_finite p σ r

/-- The actual finite logarithm transforms by the actual p-adic cyclotomic scalar. -/
theorem complexCyclotomicLog_character_finite (σ : PadicGalois p) (r : ℕ) :
    complexDeRhamFiniteEval p r (complexDeRhamGalois p σ (complexCyclotomicLog p)) =
      complexFiniteThetaQuotientScalars p r
        ((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv).val : ℚ_[p]) *
          complexDeRhamFiniteEval p r (complexCyclotomicLog p) := by
  rw [complexCyclotomicLog_galois_eval, complexCyclotomicLog_eval]
  have h := finiteNilpotentLog_pow_limit (complexCyclotomicArgument_eval_nilpotent p r)
    (complexCyclotomicExponent p σ) (complexCyclotomicExponent_tendsto_finite p σ r)
    (complexCyclotomicArgument_pow_tendsto p σ r)
  simpa only [add_sub_cancel_left] using h

end PadicHodgeTheory
