/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexFiniteThetaTopology
public import FLT.PadicHodgeTheory.ComplexThetaQuotientScalars

/-! # The existing de Rham scalar embedding has continuous finite-level components -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- Actual p-adic scalars in the finite levels, using the canonical quotient identification. -/
def complexFiniteThetaQuotientScalars (n : ℕ) : ℚ_[p] →+* ComplexFiniteThetaQuotient p n :=
  (complexFiniteThetaQuotientEquiv p n).symm.toRingHom.comp
    (complexThetaQuotientInvertPScalars p n)

/-- Each finite-level scalar map is continuous from the standard topology on Q_p. -/
theorem complexFiniteThetaQuotientScalars_continuous (n : ℕ) :
    Continuous (complexFiniteThetaQuotientScalars p n) :=
  (complexFiniteThetaQuotientHomeomorph p n).symm.continuous.comp
    (complexThetaQuotientInvertPScalars_continuous p n)

/-- Evaluation of the existing scalar embedding agrees with the coefficient construction. -/
theorem complexFiniteThetaQuotientScalars_eval (n : ℕ) (x : ℚ_[p]) :
    AdicCompletion.evalₐ (RingHom.ker (complexThetaInvertP p)) n (complexPadicToDeRham p x) =
      complexFiniteThetaQuotientScalars p n x := by
  have he : (AdicCompletion.evalₐ (RingHom.ker (complexThetaInvertP p)) n).toRingHom.comp
      (complexPadicToDeRham p) = complexFiniteThetaQuotientScalars p n := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[p])
    ext a
    apply (complexFiniteThetaQuotientEquiv p n).injective
    change complexFiniteThetaQuotientEquiv p n
      (AdicCompletion.evalₐ (RingHom.ker (complexThetaInvertP p)) n
        (complexPadicToDeRham p (algebraMap ℤ_[p] ℚ_[p] a))) =
      complexFiniteThetaQuotientEquiv p n ((complexFiniteThetaQuotientEquiv p n).symm
        (complexThetaQuotientInvertPScalars p n (algebraMap ℤ_[p] ℚ_[p] a)))
    rw [RingEquiv.apply_symm_apply, complexThetaQuotientInvertPScalars_int,
      complexPadicToDeRham_int]
    change complexFiniteThetaQuotientEquiv p n
      (AdicCompletion.evalₐ (RingHom.ker (complexThetaInvertP p)) n
        (AdicCompletion.of _ _ (algebraMap (Ainf p) (ComplexAinfInvertP p)
          (complexPadicIntToAinf p a)))) = _
    rw [AdicCompletion.evalₐ_of, complexFiniteThetaQuotientEquiv_mk,
      complexThetaQuotientLocalizationMap_algebraMap]
    rfl
  exact RingHom.congr_fun he x

/-- The actual finite evaluations of Q_p scalars are continuous. -/
theorem complexPadicToDeRham_eval_continuous (n : ℕ) :
    Continuous (fun x : ℚ_[p] ↦
      AdicCompletion.evalₐ (RingHom.ker (complexThetaInvertP p)) n (complexPadicToDeRham p x)) := by
  simp only [complexFiniteThetaQuotientScalars_eval]
  exact complexFiniteThetaQuotientScalars_continuous p n

end PadicHodgeTheory
