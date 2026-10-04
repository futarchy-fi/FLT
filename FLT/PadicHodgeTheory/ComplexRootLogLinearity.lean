/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexRootPowerConvergence
public import FLT.PadicHodgeTheory.ComplexSharpOneLogAdditivity
public import FLT.PadicHodgeTheory.FiniteLogContinuity
public import FLT.PadicHodgeTheory.PadicResidueConvergence

/-! # P-adic linearity of logarithms of actual integral root sequences -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- The logarithm of an actual compatible root sequence whose zeroth root is one. -/
def complexRootSequenceLog (s : Perfection 𝓞_ℂ_[p] p) (hs : s.val 0 = 1) :
    ComplexBDeRhamPlus p :=
  complexTiltLog p (complexRootSequenceShift p s 0)
    ((complexRootSequenceShift_sharp p s 0).trans hs)

/-- Finite evaluation of this root sequence's Teichmuller difference uses the original quotient. -/
theorem complexRootLogArgument_eval (s : Perfection 𝓞_ℂ_[p] p) (r : ℕ) :
    complexDeRhamFiniteEval p r (complexTiltLogArgument p (complexRootSequenceShift p s 0)) =
      Ideal.Quotient.mk (ComplexDeRhamIdeal p ^ r)
        (algebraMap (Ainf p) (ComplexAinfInvertP p)
          (WittVector.teichmuller p (complexRootSequenceShift p s 0))) - 1 := by
  change Ideal.Quotient.mk (ComplexDeRhamIdeal p ^ r)
    (algebraMap (Ainf p) (ComplexAinfInvertP p) _) = _
  simp only [map_sub, map_one]

/-- Actual rootwise p-adic exponentiation multiplies the convergent logarithm by that scalar. -/
theorem complexRootSequenceLog_padic (s w : Perfection 𝓞_ℂ_[p] p)
    (hs : s.val 0 = 1) (hw : w.val 0 = 1) (a : ℤ_[p])
    (ha : ∀ n, w.val n = s.val n ^ (PadicInt.toZModPow n a).val) :
    complexRootSequenceLog p w hw =
      complexPadicToDeRham p (a : ℚ_[p]) * complexRootSequenceLog p s hs := by
  apply AdicCompletion.ext_evalₐ
  intro r
  change complexDeRhamFiniteEval p r (complexRootSequenceLog p w hw) =
    complexDeRhamFiniteEval p r (_ * _)
  rw [map_mul]
  erw [complexFiniteThetaQuotientScalars_eval]
  unfold complexRootSequenceLog
  rw [complexTiltLog_eval, complexTiltLog_eval]
  have hn : complexDeRhamFiniteEval p r
      (complexTiltLogArgument p (complexRootSequenceShift p s 0)) ^ r = 0 := by
    rw [← map_pow]
    exact complexDeRhamFiniteEval_eq_zero p r (Ideal.pow_mem_pow
      (complexTiltLogArgument_mem p _ ((complexRootSequenceShift_sharp p s 0).trans hs)) r)
  have hc : Filter.Tendsto
      (fun n ↦ ((PadicInt.toZModPow n a).val : ComplexFiniteThetaQuotient p r))
      Filter.atTop (nhds (complexFiniteThetaQuotientScalars p r (a : ℚ_[p]))) := by
    have h := (complexFiniteThetaQuotientScalars_continuous p r).continuousAt.tendsto.comp
      (padicResidue_tendsto_rational p a)
    simpa only [Function.comp_def, map_natCast] using h
  have hp : Filter.Tendsto (fun n ↦
      (1 + complexDeRhamFiniteEval p r
        (complexTiltLogArgument p (complexRootSequenceShift p s 0))) ^
          (PadicInt.toZModPow n a).val) Filter.atTop
      (nhds (1 + complexDeRhamFiniteEval p r
        (complexTiltLogArgument p (complexRootSequenceShift p w 0)))) := by
    simpa only [complexRootLogArgument_eval, ← add_sub_assoc, add_sub_cancel_left] using
      complexRootPower_tendsto_finite p s w (fun n ↦ (PadicInt.toZModPow n a).val) ha r
  have h := finiteNilpotentLog_pow_limit hn (fun n ↦ (PadicInt.toZModPow n a).val) hc hp
  simpa only [add_sub_cancel_left] using h

end PadicHodgeTheory
