/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexRootPowerBounds
public import FLT.PadicHodgeTheory.ComplexFiniteThetaTopology

/-! # Powers of actual compatible roots converge at every theta level -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]
  (s w : Perfection 𝓞_ℂ_[p] p) (a : ℕ → ℕ)
  (ha : ∀ n, w.val n = s.val n ^ a n)
include ha

/-- Convergence already holds before inverting p, in each integral theta quotient. -/
theorem complexRootPower_tendsto_integral (r : ℕ) :
    Filter.Tendsto (fun n ↦
      Ideal.Quotient.mk (RingHom.ker (complexTheta p) ^ r)
        (WittVector.teichmuller p (complexRootSequenceShift p s 0)) ^
          a n) Filter.atTop
      (nhds (Ideal.Quotient.mk (RingHom.ker (complexTheta p) ^ r)
        (WittVector.teichmuller p (complexRootSequenceShift p w 0)))) := by
  apply tendsto_sub_nhds_zero_iff.mp
  have hI : IsAdic (Ideal.span {(p : ComplexIntegralThetaQuotient p r)}) := rfl
  apply hI.hasBasis_nhds_zero.tendsto_right_iff.mpr
  intro k _
  filter_upwards [Filter.eventually_ge_atTop (k + r)] with n hn
  simpa only [neg_sub, SetLike.mem_coe] using
    (Ideal.span {(p : ComplexIntegralThetaQuotient p r)} ^ k).neg_mem
    (complexRootPowerDifference_quotient_mem p s w a ha k r n (by omega))

/-- The same limit holds in the p-inverted integral coefficient quotient. -/
theorem complexRootPower_tendsto_invertP (r : ℕ) :
    Filter.Tendsto (fun n ↦
      algebraMap (ComplexIntegralThetaQuotient p r) (ComplexThetaQuotientInvertP p r)
        (Ideal.Quotient.mk (RingHom.ker (complexTheta p) ^ r)
          (WittVector.teichmuller p (complexRootSequenceShift p s 0))) ^
            a n) Filter.atTop
      (nhds (algebraMap (ComplexIntegralThetaQuotient p r) (ComplexThetaQuotientInvertP p r)
        (Ideal.Quotient.mk (RingHom.ker (complexTheta p) ^ r)
          (WittVector.teichmuller p (complexRootSequenceShift p w 0))))) := by
  have h := (complexThetaQuotientInvertP_continuous p r).continuousAt.tendsto.comp
    (complexRootPower_tendsto_integral p s w a ha r)
  simpa only [Function.comp_def, map_pow] using h

/-- Integer powers converge to the prescribed root sequence at each finite de Rham level. -/
theorem complexRootPower_tendsto_finite (r : ℕ) :
    Filter.Tendsto (fun n ↦
      Ideal.Quotient.mk (RingHom.ker (complexThetaInvertP p) ^ r)
        (algebraMap (Ainf p) (ComplexAinfInvertP p)
          (WittVector.teichmuller p (complexRootSequenceShift p s 0))) ^
            a n) Filter.atTop
      (nhds (Ideal.Quotient.mk (RingHom.ker (complexThetaInvertP p) ^ r)
        (algebraMap (Ainf p) (ComplexAinfInvertP p)
          (WittVector.teichmuller p (complexRootSequenceShift p w 0))))) := by
  apply (complexFiniteThetaQuotientHomeomorph p r).isInducing.tendsto_nhds_iff.mpr
  simpa only [Function.comp_def, complexFiniteThetaQuotientHomeomorph,
    RingEquiv.toEquiv_eq_coe, Equiv.toHomeomorphOfIsInducing_apply, RingEquiv.coe_toEquiv,
    map_pow, complexFiniteThetaQuotientEquiv_mk,
    complexThetaQuotientLocalizationMap_algebraMap] using
      complexRootPower_tendsto_invertP p s w a ha r

end PadicHodgeTheory
