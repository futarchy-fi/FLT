/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexCyclotomicPowerBounds
public import FLT.PadicHodgeTheory.ComplexFiniteThetaTopology

/-! # Integer cyclotomic powers converge to the actual Galois transform -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- Convergence already holds before inverting p, in each integral theta quotient. -/
theorem complexCyclotomicPower_tendsto_integral (σ : PadicGalois p) (r : ℕ) :
    Filter.Tendsto (fun n ↦
      Ideal.Quotient.mk (RingHom.ker (complexTheta p) ^ r)
        (WittVector.teichmuller p (complexCyclotomicTilt p)) ^
          complexCyclotomicExponent p σ n) Filter.atTop
      (nhds (Ideal.Quotient.mk (RingHom.ker (complexTheta p) ^ r)
        (WittVector.teichmuller p (complexTiltGalois p σ (complexCyclotomicTilt p))))) := by
  apply tendsto_sub_nhds_zero_iff.mp
  have hI : IsAdic (Ideal.span {(p : ComplexIntegralThetaQuotient p r)}) := rfl
  apply hI.hasBasis_nhds_zero.tendsto_right_iff.mpr
  intro k _
  filter_upwards [Filter.eventually_ge_atTop (k + r)] with n hn
  simpa only [neg_sub, SetLike.mem_coe] using
    (Ideal.span {(p : ComplexIntegralThetaQuotient p r)} ^ k).neg_mem
    (complexCyclotomicPowerDifference_quotient_mem p σ k r n (by omega))

/-- The same limit holds in the p-inverted integral coefficient quotient. -/
theorem complexCyclotomicPower_tendsto_invertP (σ : PadicGalois p) (r : ℕ) :
    Filter.Tendsto (fun n ↦
      algebraMap (ComplexIntegralThetaQuotient p r) (ComplexThetaQuotientInvertP p r)
        (Ideal.Quotient.mk (RingHom.ker (complexTheta p) ^ r)
          (WittVector.teichmuller p (complexCyclotomicTilt p))) ^
            complexCyclotomicExponent p σ n) Filter.atTop
      (nhds (algebraMap (ComplexIntegralThetaQuotient p r) (ComplexThetaQuotientInvertP p r)
        (Ideal.Quotient.mk (RingHom.ker (complexTheta p) ^ r)
          (WittVector.teichmuller p (complexTiltGalois p σ (complexCyclotomicTilt p)))))) := by
  have h := (complexThetaQuotientInvertP_continuous p r).continuousAt.tendsto.comp
    (complexCyclotomicPower_tendsto_integral p σ r)
  simpa only [Function.comp_def, map_pow] using h

/-- At the existing finite de Rham levels, integer powers converge to sigma(epsilon). -/
theorem complexCyclotomicPower_tendsto_finite (σ : PadicGalois p) (r : ℕ) :
    Filter.Tendsto (fun n ↦
      Ideal.Quotient.mk (RingHom.ker (complexThetaInvertP p) ^ r)
        (algebraMap (Ainf p) (ComplexAinfInvertP p)
          (WittVector.teichmuller p (complexCyclotomicTilt p))) ^
            complexCyclotomicExponent p σ n) Filter.atTop
      (nhds (Ideal.Quotient.mk (RingHom.ker (complexThetaInvertP p) ^ r)
        (algebraMap (Ainf p) (ComplexAinfInvertP p)
          (WittVector.teichmuller p (complexTiltGalois p σ (complexCyclotomicTilt p)))))) := by
  apply (complexFiniteThetaQuotientHomeomorph p r).isInducing.tendsto_nhds_iff.mpr
  simpa only [Function.comp_def, complexFiniteThetaQuotientHomeomorph,
    RingEquiv.toEquiv_eq_coe, Equiv.toHomeomorphOfIsInducing_apply, RingEquiv.coe_toEquiv,
    map_pow, complexFiniteThetaQuotientEquiv_mk,
    complexThetaQuotientLocalizationMap_algebraMap] using
      complexCyclotomicPower_tendsto_invertP p σ r

end PadicHodgeTheory
