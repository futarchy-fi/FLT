/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalIntegralExactness
public import FLT.GroupScheme.IntegralQuotientFaithfullyFlat

/-!
# Faithfully flat prescribed quotients over the rational prime completion

Rigidity identifies the prescribed target with the contracted quotient.
Faithful flatness therefore holds for the prescribed integral map itself.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
variable (p : ℕ) [Fact p.Prime]
local notation "O" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ (LocalCyclotomic.rationalPlace p)
local notation "K" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ (LocalCyclotomic.rationalPlace p)

/-- A generically surjective prescribed quotient onto a p-power level is faithfully flat. -/
theorem ModelHom.faithfullyFlat_of_rational_power {X Y : FF O K}
    (hp : 2 < p) (hY : KilledByPowerOf p Y) (f : ModelHom X Y)
    (hf : Function.Surjective (genericHom f)) : f.toAlgHom.toRingHom.FaithfullyFlat := by
  have hc := f.quotientComparison_bijective p hp hY hf
  have hq : ((genericHom f).toFlatQuotient hf).toAlgHom.toRingHom.FaithfullyFlat := by
    exact (genericHom f).quotientCoordinatesFaithfullyFlat
  have h := RingHom.FaithfullyFlat.stableUnderComposition
    (f.quotientComparison hf).toAlgHom.toRingHom
    ((genericHom f).toFlatQuotient hf).toAlgHom.toRingHom
    (RingHom.FaithfullyFlat.of_bijective hc) hq
  change (((genericHom f).toFlatQuotient hf).comp
    (f.quotientComparison hf)).toAlgHom.toRingHom.FaithfullyFlat at h
  rw [f.quotientComparisonComp hf] at h
  exact h

end ThreeAdicPlan
